package main

import (
    "fmt"
    "os/exec"
    "log"
    "math/rand"
    "time"
    "os"
    "errors"
    "sort"
    "math"
    "image"
    "image/color"
    "image/gif"
)
type command struct{
    name string
    numInputs int
    numOutputs int
}

func (c command) isTerminal() bool{
    return (c.numInputs == 0 && c.numInputs == 0)
}

type branch struct{
    rootCmd command
    subBranches []branch
    lastFitness float32
}

func (b branch) getString() string{
    var s string
    if !b.rootCmd.isTerminal(){
        s += "("
    }
    s += b.rootCmd.name
    for i := 0; i < len(b.subBranches); i++{
        s += " "
        s += b.subBranches[i].getString()
    }
    if !b.rootCmd.isTerminal(){
        s += ")"
    }
    return s
}

func (b branch) deepCopy() branch{
    var L []branch
    for i := 0; i < len(b.subBranches); i++{
        L = append(L, b.subBranches[i].deepCopy())
    }
    cpy := branch{b.rootCmd, L, b.lastFitness}
    return cpy
}

func (b branch) getMutation(chance float32) branch{
    cpy := b.deepCopy()
    if(rand.Float32() <= chance){
        cmd := commands[rand.Intn(len(commands))]
        for (cmd.numOutputs != cpy.rootCmd.numOutputs || cmd.numInputs != cpy.rootCmd.numInputs) {
            cmd = commands[rand.Intn(len(commands))]
        }
        cpy.rootCmd = cmd
        return cpy;
    }
    for i := 0; i < len(cpy.subBranches); i++{
        cpy.subBranches[i] = cpy.subBranches[i].getMutation(chance);
    }
    return cpy
}

func (b branch) getNumNodes() int{
    num := 1
    for i := 0; i < len(b.subBranches); i++{
        num += b.subBranches[i].getNumNodes()
    }
    return num
}

func (b branch) getRandomBranch() (branch, int){
    numNodes := b.getNumNodes()
    chance := 1.0 / float32(numNodes - 1)
    par, idx, err := b.getRandomBranchHelper(chance)
    if err != nil{
        return b, 0
    }
    return par, idx
}

func (b branch) getRandomBranchHelper(chance float32) (branch, int, error){
    for i := 0; i < len(b.subBranches); i++{
        if rand.Float32() < chance{
            return b, i, nil
        }
        res,idx,err := b.subBranches[i].getRandomBranchHelper(chance)
        if err == nil{
            return res, idx, nil
        }
    }
    dummy := branch{}
    return dummy, 0, errors.New("Nothing")
}

func (a branch) getCrossoverPair(b branch) (branch, branch){
    cpyA := a.deepCopy()
    cpyB := b.deepCopy()
    parA, idxA := cpyA.getRandomBranch()
    parB, idxB := cpyB.getRandomBranch()
    tmp := parB.subBranches[idxB]
    parB.subBranches[idxB] = parA.subBranches[idxA]
    parA.subBranches[idxA] = tmp
    return cpyA, cpyB
}

func genRandomBranch(bType int) branch{
    var possibleCommands []command
    possibleCommands = getCommandsFromInt(bType)
    root := possibleCommands[rand.Intn(len(possibleCommands))]
    var sub []branch
    for i := 0; i < root.numInputs; i++{
        sub = append(sub, genRandomBranch(IN | FLEX | FUNC))
    }
    for i := 0; i < root.numOutputs; i++{
        sub = append(sub, genRandomBranch(OUT | FUNC))
    }
    b := branch{root, sub, 0}
    return b
}

func checkError(err error){
    if err != nil {
        log.Fatal(err)
    }
}

func getCommandsFromInt(n int) []command{
    var L []command
    if n & IN == IN{
        L = append(L, inputCommands...)
    }
    if n & OUT == OUT{
        L = append(L, outputCommands...)
    }
    if n & FLEX == FLEX{
        L = append(L, flexibleCommands...)
    }
    if n & FUNC == FUNC{
        L = append(L, functionCommands...)
    }
    return L
}

func getLispBool(b bool) string{
    if(b){
        return "t"
    } else{
        return "nil"
    }
}

func (b branch) getFitness(w, h int) float32{
    x := 0
    y := 0
    aBool := false
    bBool := false
    var visitedMap []bool
    var boolCheckMap []int
    for i := 0; i < w * h; i++{
        visitedMap = append(visitedMap, false)
        boolCheckMap = append(boolCheckMap, -1)
    }
    var fitness float32
    fitness = 0.0
    count := 0
    visitedMap[x + y * w] = true
    isDone := false
    for !isDone{
        fp, err := os.Create("out.lisp")
        checkError(err)
        defer fp.Close()
        _, err = fp.WriteString("(defvar n " + getLispBool(y == 0) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar ne " + getLispBool(y == 0 && x == w-1) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar e " + getLispBool(x == w-1) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar se " + getLispBool(y == h-1 && x == w-1) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar s " + getLispBool(y == h-1) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar sw " + getLispBool(y == h-1 && x == 0) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar w " + getLispBool(x == 0) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar nw " + getLispBool(y == 0 && x == 0) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar a " + getLispBool(aBool) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar b " + getLispBool(bBool) + ")\n")
        checkError(err)
        _, err = fp.WriteString(b.getString() + "\n")
        checkError(err)
        cmd := exec.Command("sbcl", "--script", "out.lisp")
        out, err := cmd.Output()
        checkError(err)
        if(len(out) < 1){
            isDone = true
            break
        }
        c := out[0]
        if c == 'n'{
            y--
        }else if c == 's'{
            y++
        }else if c == 'e'{
            x++
        }else if c == 'w'{
            x--
        }else if c == 'a'{
            aBool = !aBool
        }else if c == 'b'{
            bBool = !bBool
        }else{
            isDone = true
            break
        }
        if x < 0 || x >= w || y < 0 || y >= h {
            isDone = true
            break
        }else if(!visitedMap[x + y * w]){
            visitedMap[x + y * w] = true
            fitness++
            if(fitness == float32(w * h)){
                isDone = true
                break
            }
        }
        boolChecker := 0
        if aBool{
            boolChecker |= 1
        }
        if bBool{
            boolChecker |= 2
        }
        if boolCheckMap[x + y * w] == boolChecker{
            fitness -= 0.1
        } else {
            boolCheckMap[x + y * w] = boolChecker
        }
        count++
        if float32(count) > float32(width * height) * 1.2{
            isDone = true
            break
        }
    }
    return fitness
}

func genImage(w, h, tileW, x, y int, visited []bool) *image.Paletted{
    var palette = []color.Color{
        color.RGBA{0x00, 0x00, 0x00, 0xff},
        color.RGBA{0xff, 0xff, 0xff, 0xff},
        color.RGBA{0xff, 0xff, 0x00, 0xff},
        color.RGBA{0xff, 0x00, 0x00, 0xff},
    }
    img := image.NewPaletted(image.Rect(0, 0, (w+2) * tileW, (h+2) * tileW), palette)
    for i := 0; i < (w+2) * tileW; i++{
        for j := 0; j < (h+2) * tileW; j++{
            img.Set(i,j, color.RGBA{0,0,0,255})
        }
    }
    for i := 0; i < w; i++{
        for j := 0; j < h; j++{
            var col color.Color
            if visited[i + j * w]{
                col = color.RGBA{255, 255, 0, 255}
            }else{
                col = color.RGBA{255, 255, 255, 255}
            }
            for ii := (i+1) * tileW; ii < (i+2) * tileW; ii++{
                for jj := (j+1) * tileW; jj < (j+2) * tileW; jj++{
                    img.Set(ii,jj,col)
                }
            }
        }
    }
    for i := (x+1) * tileW; i < (x+2) * tileW; i++{
        for j := (y+1) * tileW; j < (y+2) * tileW; j++{
            img.Set(i,j, color.RGBA{255,0,0,255})
        }
    }
    return img
}

func (b branch) genGIF(w, h int, filename string) {
    //Some GIF initialization. 
    //Coming from a tutorial:
    // http://tech.nitoyon.com/en/blog/2016/01/07/go-animated-gif-gen/

    var images[]*image.Paletted
    var delays[]int
    tileWidth := 64
    x := 0
    y := 0
    aBool := false
    bBool := false
    var visitedMap []bool
    for i := 0; i < w * h; i++{
        visitedMap = append(visitedMap, false)
    }
    fitness := 0
    count := 0
    isDone := false

    visitedMap[x + y * w] = true
    img := genImage(w, h, tileWidth, x, y, visitedMap)
    images = append(images, img)
    delays = append(delays, 1)

    for !isDone{
        fp, err := os.Create("out3.lisp")
        checkError(err)
        defer fp.Close()
        _, err = fp.WriteString("(defvar n " + getLispBool(y == 0) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar ne " + getLispBool(y == 0 && x == w-1) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar e " + getLispBool(x == w-1) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar se " + getLispBool(y == h-1 && x == w-1) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar s " + getLispBool(y == h-1) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar sw " + getLispBool(y == h-1 && x == 0) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar w " + getLispBool(x == 0) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar nw " + getLispBool(y == 0 && x == 0) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar a " + getLispBool(aBool) + ")\n")
        checkError(err)
        _, err = fp.WriteString("(defvar b " + getLispBool(bBool) + ")\n")
        checkError(err)
        _, err = fp.WriteString(b.getString() + "\n")
        checkError(err)
        cmd := exec.Command("sbcl", "--script", "out3.lisp")
        out, err := cmd.Output()
        checkError(err)
        if(len(out) < 1){
            isDone = true
            break
        }
        c := out[0]
        if c == 'n'{
            y--
        }else if c == 's'{
            y++
        }else if c == 'e'{
            x++
        }else if c == 'w'{
            x--
        }else if c == 'a'{
            aBool = !aBool
        }else if c == 'b'{
            bBool = !bBool
        }else{
            isDone = true
            break
        }
        if x < 0 || x >= w || y < 0 || y >= h {
            isDone = true
            break
        }else if(!visitedMap[x + y * w]){
            visitedMap[x + y * w] = true
            fitness++
            if(fitness == w * h){
                isDone = true
                break
            }
        }
        count++
        if float32(count) > float32(width * height) * 1.2{
            isDone = true
            break
        }
        img = genImage(w, h, tileWidth, x, y, visitedMap)
        images = append(images, img)
        delays = append(delays, 1)
    }
    img = genImage(w, h, tileWidth, x, y, visitedMap)
    images = append(images, img)
    delays = append(delays, 1)
    imgFp, err := os.OpenFile(filename, os.O_WRONLY|os.O_CREATE, 0600)
    checkError(err)
    defer imgFp.Close()
    gif.EncodeAll(imgFp, &gif.GIF{
        Image: images,
        Delay: delays,
    })
}


func gauss(max int, stddev float64) int{
    f := math.Abs(rand.NormFloat64() * stddev)
    for f > 1{
        f -= 1
    }
    v := f * float64(max)
    val := int(math.Floor(v))

    if val >= max{
        val = max - 1
    }
    return val
}

var commands []command
var inputCommands []command
var outputCommands []command
var flexibleCommands []command
var functionCommands []command
var IN int
var OUT int
var FLEX int
var FUNC int
var width int
var height int
var popSize int

func main(){
    rand.Seed(time.Now().UTC().UnixNano());
    IN = 1
    OUT = 2
    FLEX = 4
    FUNC = 8

    width = 6
    height = 4
    popSize = 4000
    fmt.Printf("Running...\n");

    c_and := command{"AND", 2, 0}
    c_or := command{"OR", 2, 0}
    c_not := command{"NOT", 1, 0}
    c_if := command{"IF", 1, 2}
    commandsL := []command{c_and, c_or, c_not, c_if}
    for i := 0; i < len(commandsL); i++{
        commands = append(commands, commandsL[i])
    }

    flexibleCommands = append(flexibleCommands, c_and)
    flexibleCommands = append(flexibleCommands, c_or)
    flexibleCommands = append(flexibleCommands, c_not)
    functionCommands = append(flexibleCommands, c_if)

    inputs := []string{"n", "ne", "e", "se", "s", "sw", "w", "nw", "b", "a"}
    outputs := []string{"n", "e", "w", "b", "s", "a"}
    for i := 0; i < len(inputs); i++{
        commands = append(commands, command{inputs[i], 0, 0})
        inputCommands = append(inputCommands, command{inputs[i], 0 , 0})
    }
    for i := 0; i < len(outputs); i++{
        commands = append(commands, command{"(write-line \"" + outputs[i] + "\")", 0 , 0})
        outputCommands = append(outputCommands, command{"(write-line \"" + outputs[i] + "\")", 0 , 0})
    }
    var maxFitness float32
    maxFitness = 0.0
    var pop []branch
    curGen := 0

    for i := 0; i < popSize; i++{
        tmp := genRandomBranch(FLEX | FUNC)
        pop = append(pop, tmp)
    }

    for maxFitness < float32(width * height){
        for i := 0; i < popSize; i++{
            fit := pop[i].getFitness(width, height);
            //fmt.Printf("%d) %d\n", i, fit);
            pop[i].lastFitness = fit;
            if i % (popSize / 10) == 0{
                fmt.Printf("#");
            }
        }
        fmt.Printf("\n");
        sort.Slice(pop, func(i,j int) bool{
            return pop[i].lastFitness > pop[j].lastFitness
        })
        maxFitness = pop[0].lastFitness
        var L []branch
        for i := 0; i < (popSize / 10); i++{
            L = append(L, pop[i]);
        }
        for i := 0; i < (2 * popSize / 10); i++{
            val := gauss(popSize, 0.05)
            L = append(L, pop[val].getMutation(0.2))
        }
        for i := 0; i < (7 * popSize / 10) / 2; i++{
            val1 := gauss(popSize, 0.05)
            val2 := gauss(popSize, 0.05)
            a,b := pop[val1].getCrossoverPair(pop[val2])
            L = append(L, a)
            L = append(L, b)
        }
        fmt.Printf("Generation %d best: %f\n", curGen, maxFitness)
        fmt.Printf("Best code: %s\n", pop[0].getString());
        pop[0].genGIF(width, height, "Gen_" + fmt.Sprintf("%d", curGen) + ".gif")
        pop = L
        curGen++
    }
}
