-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_theorem_2_1
-- name    : DynMaxMatchEC.Main.theorem_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:19.222247+00:00
-- url     : https://prove2.me/theorems/7daf44b2-1956-4c1f-a0b7-6ea83cd10e1e
-- title:
--   Theorem 2.1 — deterministic (∆ + 1)-edge-coloring of a static graph in O(m·2^{O(√log ∆)}·log n) time ([ABB+26])
-- statement:
--   There is a deterministic algorithm that, given a simple graph $G$ with $n$ vertices, $m$ edges and maximum degree $\Delta$, computes an edge coloring of $G$ with $\Delta+1$ colors in time
--   $$O\big(m\cdot2^{O(\sqrt{\log\Delta})}\cdot\log n\big).$$
--   In Lean: a program without random instructions, a word-size constant $a$ and constants $K,C$ such that, given the words $n$, $m$ and the $m$ edges (words of $a\lceil\log_2(n^2+1)\rceil$ bits), the program halts within $K(m+1)\,2^{C\sqrt{\log_2\Delta}}(1+\log_2 n)$ steps and the color records it has written form a proper $(\Delta+1)$-edge-coloring of $G$. This is Theorem 1.1 of Assadi et al. [ABB+26], quoted without proof; Theorems C.1 and 5.1 use it for their initial colorings.
--
--   Differences from the source:
--   - encoding: an algorithm (no machine model named; word-RAM data structures with O(log n)-bit words) → a program of the published word RAM DynBrooks_Machine (unit-cost uniform random words, blocking read, write, halt, one step per instruction) with word size a·⌈log₂(n² + 1)⌉, the constant a chosen with the program; reason: the paper's data structures (search trees, heaps, arrays) are word-RAM structures; unbounded words would trivialize the bounds
--   - encoding: given a simple n-vertex m-edge graph; computes an edge coloring → input words n, m and an edge list in any order and orientation; the program halts, and its output, read as color records u, v, c, is the coloring; reason: a static algorithm on the same machine as the dynamic ones
--   - reading: running time O(m·2^{O(√log ∆)}·log n) → at most K·(m + 1)·2^{C·√(log₂ ∆)}·(1 + log₂ n) steps, K and C absolute; reason: the printed bound is 0 when m = 0 or n = 1, where reading the input already costs steps; for m ≥ 1 and n ≥ 2 the two bounds differ by a factor at most 4
--   - encoding: a deterministic algorithm → a program with no coin instruction, the bound holding on every tape; reason: the machine's only randomness is the coin instruction
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 11, Theorem 2.1 (Theorem 1.1 of [ABB+26])

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_EdgeColoring

open DynBrooks Filter Topology

namespace DynMaxMatchEC.Main

/-- **Theorem 2.1** (Theorem 1.1 of [ABB+26]; Chuzhoy, manuscript Nov. 1, 2026, PDF sha256
2c277528…4ca5, p. 11). There are a coin-free program, a word-size constant `a` and constants
`K, C` such that, for every `n`, every simple graph `G` on `Fin n` with `m` edges and maximum
degree `Δ`, given as the words `n, m` and an edge list (word size `a·⌈log₂(n² + 1)⌉`), the program
halts within `K·(m + 1)·2^{C√(log₂ Δ)}·(1 + log₂ n)` steps, and the output, read as color records,
is an edge coloring of `G` with `Δ + 1` colors. (Reading: the source's `O(m·2^{O(√log Δ)}·log n)`
with `m + 1` and `1 + log₂ n` in place of `m` and `log₂ n`, which differ only when `m = 0` or
`n = 1`, where the printed bound is `0`.) -/
theorem theorem_2_1 :
    ∃ (P : Program) (a K C : ℕ), CoinFree P ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (es : List (Fin n × Fin n)), IsEdgeList G es →
        ∀ ω : ℕ → BitVec (wordSize a (n * n)),
          ∃ s : ℕ,
            (s : ℝ) ≤ (K : ℝ) * (es.length + 1) *
                (2 : ℝ) ^ ((C : ℝ) * Real.sqrt (Real.logb 2 (maxDeg G))) * (1 + Real.logb 2 n) ∧
              IsHalted P (run P ω (initConfig (wordSize a (n * n)) (n :: edgeWords es)) s) ∧
              IsProperEdgeColoring ((maxDeg G : ℝ) + 1) G
                (reportedColoring n
                  (run P ω (initConfig (wordSize a (n * n)) (n :: edgeWords es)) s).output) := by sorry

end DynMaxMatchEC.Main
