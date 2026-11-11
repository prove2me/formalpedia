-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_theorem_1_2_c
-- name    : DynMaxMatchEC.Main.theorem_1_2_c
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:15.801834+00:00
-- url     : https://prove2.me/theorems/f2cf5756-2a0c-4b51-8e76-91e86913e3fe
-- title:
--   Theorem 1.2(c) — deterministic (∆ + n^{o(1)})-edge-coloring with update time O(∆⁵ n^{o(1)}) and recourse O(∆² n^{o(1)})
-- statement:
--   There is a deterministic algorithm that receives an $n$-vertex graph $G$ with $m_0$ edges and an integer $0<\Delta\le n$ bounding the maximum degree at all times under edge insertions and deletions chosen by an adaptive adversary, and maintains a $(\Delta+n^{o(1)})$-edge-coloring of $G$, with initialization time $O((n\Delta^3+m_0)\,n^{o(1)})$ ($\tilde O(n)$ if $m_0=0$), worst-case update time
--   $$O\big(\Delta^5\cdot n^{o(1)}\big)$$
--   and recourse $O(\Delta^2n^{o(1)})$, outputting after every update all edges whose colors changed with their new colors and the color of an inserted edge. In §3.2 it colors the sparsifier $G'$ for the deterministic matching algorithm; its update time is the bottleneck of Theorem 1.1(b).
--
--   Differences from the source:
--   - encoding: an algorithm (no machine model named; word-RAM data structures with O(log n)-bit words) → a program of the published word RAM DynBrooks_Machine (unit-cost uniform random words, blocking read, write, halt, one step per instruction) with word size a·⌈log₂(n² + 1)⌉, the constant a chosen with the program; reason: the paper's data structures (search trees, heaps, arrays) are word-RAM structures; unbounded words would trivialize the bounds
--   - encoding: input: an n-vertex graph with m₀ initial edges and the parameters → the words n, ∆, m₀ and an edge list of G₀ in any order and orientation; reason: machine input
--   - encoding: the maximum vertex degree is at most ∆ at all times → G₀ has maximum degree at most ∆, and an update after which some degree exceeds ∆ is illegal and ends the interaction; reason: the guarantee is required only on legal sequences
--   - encoding: online updates chosen by an adaptive adversary (updates may depend on the algorithm's prior decisions and internal state) → for every deterministic strategy mapping the list of completed configurations (memory, program counter, output, coin cursor; never the unread coins) to the next update or to stop; a proposal that is not legal for the current graph ends the interaction; reason: a randomized adversary is a mixture of deterministic ones whose coins are independent of the algorithm's, so quantifying over deterministic strategies gives the same statement
--   - encoding: a deterministic algorithm → a program with no coin instruction; every guarantee on every tape; every update completes; reason: the machine's only randomness is the coin instruction
--   - encoding: a (∆ + n^{o(1)})-edge-coloring → colors c with 1 ≤ c ≤ ∆ + n^{f(n)}, the same f as in the time bounds; reason: one f → 0 serves all n^{o(1)} terms
--   - encoding: maintains a (∆ + n^{f(n)})-edge-coloring and outputs, after every update, all edges whose colors changed with their new colors and the color of a newly inserted edge → the coloring is the uncolored assignment with every output record u, v, c applied in order; after preprocessing and after every completed update it is a proper (∆ + n^{f(n)})-edge-coloring of the current graph; reason: the coloring is read from the log, so every color change must be written; the color of an inserted edge is the last color written for that pair, so the log states it (an edge re-inserted after a deletion keeps the color last written for it unless a new record is written, and that color must then be proper); the initial coloring of G₀ is written in preprocessing
--   - encoding: recourse: the number of edges whose color may change after an update → the number of color records written while processing the update; reason: every change must be written as a record; the algorithm writes its changes and the new edge's color, which the constants absorb
--   - encoding: initialization time → preprocessing (the run from the start configuration with the input words pending) reaches a completed state within the bound on every coin tape; reason: a completed state is the machine blocked at read waiting for the first update
--   - encoding: worst-case update time and recourse → every delivered update's processing ends within the bound, and writes at most the stated number of records, on every coin tape; reason: worst-case means every update of every run, not an average
--   - encoding: O(·) and Õ(·) bounds → K·g and K·g·(1 + log₂ n)^k with natural constants K, k chosen with the program, before n and every other input; reason: the standard meaning of the asymptotic notation; 1 + log₂ n instead of log₂ n only matters at n = 1, where the printed polylogarithmic factor is 0
--   - encoding: n^{o(1)} factors → n^{f(n)} for one function f : ℕ → ℝ with f(n) → 0, chosen with the program before n and every other input; reason: the standard meaning of n^{o(1)}; one f serves all occurrences since the bounds are monotone in f
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 4, Theorem 1.2(c)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_EdgeColoring

open DynBrooks Filter Topology

namespace DynMaxMatchEC.Main

/-- **Theorem 1.2(c)** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 4). There are
a coin-free program, a word-size constant `a`, constants `K, k` and `f → 0` such that for every
`n`, every integer `0 < Δ ≤ n`, every initial graph `G₀` of maximum degree at most `Δ` with `m₀`
edges (given as the words `n, Δ`, `m₀` and an edge list), every adaptive strategy whose updates
keep every degree at most `Δ`, and every tape: preprocessing completes within
`K·(nΔ³ + m₀)·n^{f(n)}` steps, and within `K·n·(1 + log₂ n)^k` steps if `m₀ = 0`; every delivered
update completes within `K·Δ⁵·n^{f(n)}` steps having written at most `K·Δ²·n^{f(n)}` color records;
and the reported coloring is always a proper `(Δ + n^{f(n)})`-edge-coloring of the current graph. -/
theorem theorem_1_2_c :
    ∃ (P : Program) (a K k : ℕ) (f : ℕ → ℝ), CoinFree P ∧ Tendsto f atTop (𝓝 0) ∧
      ∀ (n Δ : ℕ), 0 < Δ → Δ ≤ n →
        ∀ (G₀ : SimpleGraph (Fin n)), MaxDegLE Δ G₀ →
        ∀ (es : List (Fin n × Fin n)), IsEdgeList G₀ es →
        ∀ (A : Strategy (wordSize a (n * n)) n) (ω : ℕ → BitVec (wordSize a (n * n))),
          (Setup.mk P ([n, Δ] ++ edgeWords es) G₀ (IsDegLegal Δ) A).PreprocWithin ω
              ((K : ℝ) * ((n : ℝ) * (Δ : ℝ) ^ 3 + es.length) * (n : ℝ) ^ f n) ∧
          (es.length = 0 →
            (Setup.mk P ([n, Δ] ++ edgeWords es) G₀ (IsDegLegal Δ) A).PreprocWithin ω
              ((K : ℝ) * n * (1 + Real.logb 2 n) ^ k)) ∧
          (Setup.mk P ([n, Δ] ++ edgeWords es) G₀ (IsDegLegal Δ) A).UpdatesCompleteWithin ω
              ((K : ℝ) * (Δ : ℝ) ^ 5 * (n : ℝ) ^ f n) ∧
          (Setup.mk P ([n, Δ] ++ edgeWords es) G₀ (IsDegLegal Δ) A).RecordsWithin ω
              ((K : ℝ) * (Δ : ℝ) ^ 2 * (n : ℝ) ^ f n) ∧
          (Setup.mk P ([n, Δ] ++ edgeWords es) G₀ (IsDegLegal Δ) A).AlwaysHolds ω
              (ColoringOK ((Δ : ℝ) + (n : ℝ) ^ f n)) := by sorry

end DynMaxMatchEC.Main
