-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_theorem_5_1
-- name    : DynMaxMatchEC.Main.theorem_5_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:35.757429+00:00
-- url     : https://prove2.me/theorems/c4d0cbe1-dd9a-4fa4-b92a-19a9ad7b8d91
-- title:
--   Theorem 5.1 — deterministic (z + x)-edge-coloring with update time O(z⁵ n^{o(1)}) and recourse O(z² n^{o(1)}) for n^{14/log log n} ≤ x ≤ √z ≤ √n
-- statement:
--   Let $x,z$ be integers with $n^{14/\log_2\log_2 n}\le x\le\sqrt z\le\sqrt n$. There is a deterministic algorithm that receives an $n$-vertex graph $G$ with $m_0$ edges, then edge insertions and deletions keeping the maximum degree at most $z$, and maintains a $(z+x)$-edge-coloring of $G$, outputting after every update all edges whose colors changed with their new colors and the color of an inserted edge. Its initialization time is $O((nz^3x+m_0)\,n^{o(1)})$, and $\tilde O(n)$ if $m_0=0$; its worst-case update time is
--   $$O\big(z^5\cdot n^{o(1)}\big),$$
--   and its recourse is $O(z^2n^{o(1)})$. Theorem 1.2(c) follows with $x=\lceil n^{14/\log\log n}\rceil$, $z=\max(\Delta,x^2)$.
--
--   Differences from the source:
--   - encoding: an algorithm (no machine model named; word-RAM data structures with O(log n)-bit words) → a program of the published word RAM DynBrooks_Machine (unit-cost uniform random words, blocking read, write, halt, one step per instruction) with word size a·⌈log₂(n² + 1)⌉, the constant a chosen with the program; reason: the paper's data structures (search trees, heaps, arrays) are word-RAM structures; unbounded words would trivialize the bounds
--   - encoding: input: an n-vertex graph with m₀ initial edges and the parameters → the words n, x, z, m₀ and an edge list of G₀ in any order and orientation; reason: machine input
--   - encoding: the maximum vertex degree is at most z at all times → G₀ has maximum degree at most z, and an update after which some degree exceeds z is illegal and ends the interaction; reason: the guarantee is required only on legal sequences
--   - encoding: online updates (deterministic algorithm) → for every strategy mapping completed configurations to the next update; an illegal proposal ends the interaction; reason: a deterministic algorithm's guarantee against every update sequence, adaptive or not
--   - encoding: n^{14/log log n} ≤ x, logarithms to base 2 → 3 ≤ n and (n:ℝ)^(14 / log₂(log₂ n)) ≤ x; reason: at n = 2, log log n = 0 and the printed hypothesis cannot hold; Lean's 14/0 = 0 would turn it into 1 ≤ x, so n = 2 is excluded
--   - encoding: a deterministic algorithm → a program with no coin instruction; every guarantee on every tape; every update completes; reason: the machine's only randomness is the coin instruction
--   - encoding: maintains a (z + x)-edge-coloring and outputs, after every update, all edges whose colors changed with their new colors and the color of a newly inserted edge → the coloring is the uncolored assignment with every output record u, v, c applied in order; after preprocessing and after every completed update it is a proper (z + x)-edge-coloring of the current graph; reason: the coloring is read from the log, so every color change must be written; the color of an inserted edge is the last color written for that pair, so the log states it (an edge re-inserted after a deletion keeps the color last written for it unless a new record is written, and that color must then be proper); the initial coloring of G₀ is written in preprocessing
--   - encoding: recourse: the number of edges whose color may change after an update → the number of color records written while processing the update; reason: every change must be written as a record; the algorithm writes its changes and the new edge's color, which the constants absorb
--   - encoding: initialization time → preprocessing (the run from the start configuration with the input words pending) reaches a completed state within the bound on every coin tape; reason: a completed state is the machine blocked at read waiting for the first update
--   - encoding: worst-case update time and recourse → every delivered update's processing ends within the bound, and writes at most the stated number of records, on every coin tape; reason: worst-case means every update of every run, not an average
--   - encoding: O(·) and Õ(·) bounds → K·g and K·g·(1 + log₂ n)^k with natural constants K, k chosen with the program, before n and every other input; reason: the standard meaning of the asymptotic notation; 1 + log₂ n instead of log₂ n only matters at n = 1, where the printed polylogarithmic factor is 0
--   - encoding: n^{o(1)} factors → n^{f(n)} for one function f : ℕ → ℝ with f(n) → 0, chosen with the program before n and every other input; reason: the standard meaning of n^{o(1)}; one f serves all occurrences since the bounds are monotone in f
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 59, Theorem 5.1

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_EdgeColoring

open DynBrooks Filter Topology

namespace DynMaxMatchEC.Main

/-- **Theorem 5.1** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 59). There are a
coin-free program, a word-size constant `a`, constants `K, k` and `f → 0` such that for every
`n ≥ 3` and all integers `x, z` with `n^{14/log₂ log₂ n} ≤ x ≤ √z ≤ √n`, every initial graph `G₀`
of maximum degree at most `z` with `m₀` edges (given as the words `n, x, z`, `m₀` and an edge
list), every strategy whose updates keep every degree at most `z`, and every tape: preprocessing
completes within `K·(n z³ x + m₀)·n^{f(n)}` steps, and within `K·n·(1 + log₂ n)^k` steps if
`m₀ = 0`; every delivered update completes within `K·z⁵·n^{f(n)}` steps having written at most
`K·z²·n^{f(n)}` color records; and the reported coloring is always a proper `(z + x)`-edge-coloring of
the current graph. (At `n = 2` the hypothesis `n^{14/log log n} ≤ x` cannot hold, since
`log₂ log₂ 2 = 0`; this case is excluded by `3 ≤ n`.) -/
theorem theorem_5_1 :
    ∃ (P : Program) (a K k : ℕ) (f : ℕ → ℝ), CoinFree P ∧ Tendsto f atTop (𝓝 0) ∧
      ∀ (n x z : ℕ), 3 ≤ n →
        (n : ℝ) ^ (14 / Real.logb 2 (Real.logb 2 n)) ≤ x → (x : ℝ) ≤ Real.sqrt z →
        Real.sqrt z ≤ Real.sqrt n →
        ∀ (G₀ : SimpleGraph (Fin n)), MaxDegLE z G₀ →
        ∀ (es : List (Fin n × Fin n)), IsEdgeList G₀ es →
        ∀ (A : Strategy (wordSize a (n * n)) n) (ω : ℕ → BitVec (wordSize a (n * n))),
          (Setup.mk P ([n, x, z] ++ edgeWords es) G₀ (IsDegLegal z) A).PreprocWithin ω
              ((K : ℝ) * ((n : ℝ) * (z : ℝ) ^ 3 * x + es.length) * (n : ℝ) ^ f n) ∧
          (es.length = 0 →
            (Setup.mk P ([n, x, z] ++ edgeWords es) G₀ (IsDegLegal z) A).PreprocWithin ω
              ((K : ℝ) * n * (1 + Real.logb 2 n) ^ k)) ∧
          (Setup.mk P ([n, x, z] ++ edgeWords es) G₀ (IsDegLegal z) A).UpdatesCompleteWithin ω
              ((K : ℝ) * (z : ℝ) ^ 5 * (n : ℝ) ^ f n) ∧
          (Setup.mk P ([n, x, z] ++ edgeWords es) G₀ (IsDegLegal z) A).RecordsWithin ω
              ((K : ℝ) * (z : ℝ) ^ 2 * (n : ℝ) ^ f n) ∧
          (Setup.mk P ([n, x, z] ++ edgeWords es) G₀ (IsDegLegal z) A).AlwaysHolds ω
              (ColoringOK ((z : ℝ) + x)) := by sorry

end DynMaxMatchEC.Main
