-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_theorem_C_1
-- name    : DynMaxMatchEC.Main.theorem_C_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:15.435635+00:00
-- url     : https://prove2.me/theorems/7ee635a2-8aa3-401f-a251-8b4b33780965
-- title:
--   Theorem C.1 — randomized (z + x)-edge-coloring against an adaptive adversary with recourse O(z n^{o(1)}/x) and update time O((z/x) n^{o(1)} log(1/p))
-- statement:
--   Let $0<p\le1/2$ and let $1<x\le z\le n$ be integers with $x\ge\sqrt z\cdot2^{50\sqrt{\log_2 n}}$. There is a randomized algorithm that receives an $n$-vertex graph $G$ with $m_0$ edges whose maximum degree stays at most $z$ under updates chosen by an adaptive adversary, and maintains a $(z+x)$-edge-coloring of $G$ as long as it does not return FAIL, outputting after every update every edge whose color changed (with its new color) and the color of an inserted edge. For every $t\ge1$ the probability that it returns FAIL on the $t$-th update is at most $p$. At most $O(zn^{o(1)}/x)$ edges change color per update, initialization takes $\tilde O(n)+O(m_0n^{o(1)})$ time and every update
--   $$O\Big(\frac zx\cdot n^{o(1)}\cdot\log(1/p)\Big)$$
--   time. Theorem 1.2(b) follows with $\Delta=z$, $\varepsilon=x/z$.
--
--   Differences from the source:
--   - encoding: an algorithm (no machine model named; word-RAM data structures with O(log n)-bit words) → a program of the published word RAM DynBrooks_Machine (unit-cost uniform random words, blocking read, write, halt, one step per instruction) with word size a·⌈log₂(n² + L + 1)⌉, the constant a chosen with the program; reason: the paper's data structures (search trees, heaps, arrays) are word-RAM structures; unbounded words would trivialize the bounds
--   - encoding: input: an n-vertex graph with m₀ initial edges and the parameters → the words n, x, z, L = ⌈log₂(1/p)⌉, m₀ and an edge list of G₀ in any order and orientation; reason: machine input
--   - encoding: the parameter 0 < p ≤ 1/2 → the input word L = ⌈log₂(1/p)⌉; the bounds are stated with the real p; reason: a real number is not a machine word; the program gets less information than p, so the statement is at least as strong
--   - encoding: the maximum vertex degree is at most z at all times → G₀ has maximum degree at most z, and an update after which some degree exceeds z is illegal and ends the interaction; reason: the guarantee is required only on legal sequences
--   - encoding: online updates chosen by an adaptive adversary (updates may depend on the algorithm's prior decisions and internal state) → for every deterministic strategy mapping the list of completed configurations (memory, program counter, output, coin cursor; never the unread coins) to the next update or to stop; a proposal that is not legal for the current graph ends the interaction; reason: a randomized adversary is a mixture of deterministic ones whose coins are independent of the algorithm's, so quantifying over deterministic strategies gives the same statement
--   - encoding: the algorithm returns FAIL → the program executes halt while processing an update; the interaction then stops; reason: a halted configuration never reaches a completed state again
--   - encoding: per-update failure probability p: for all t, the probability of returning FAIL while processing the t-th update is at most p → for every t ≥ 1, coinMeasure of {ω : update t is delivered and its processing executes halt} ≤ p, and every other guarantee holds on every coin tape; reason: the definition on p. 2; the measure is applied to the event as a set (outer measure), which is at least as strong
--   - encoding: maintains a (z + x)-edge-coloring and outputs, after every update, all edges whose colors changed with their new colors and the color of a newly inserted edge → the coloring is the uncolored assignment with every output record u, v, c applied in order; after preprocessing and after every completed update it is a proper (z + x)-edge-coloring of the current graph; reason: the coloring is read from the log, so every color change must be written; the color of an inserted edge is the last color written for that pair, so the log states it (an edge re-inserted after a deletion keeps the color last written for it unless a new record is written, and that color must then be proper); the initial coloring of G₀ is written in preprocessing
--   - encoding: recourse: the number of edges whose color may change after an update → the number of color records written while processing the update; reason: every change must be written as a record; the algorithm writes its changes and the new edge's color, which the constants absorb
--   - encoding: initialization time → preprocessing (the run from the start configuration with the input words pending) reaches a completed state within the bound on every coin tape; reason: a completed state is the machine blocked at read waiting for the first update
--   - encoding: worst-case update time and recourse → every delivered update's processing ends within the bound, and writes at most the stated number of records, on every coin tape; reason: worst-case means every update of every run, not an average
--   - encoding: O(·) and Õ(·) bounds → K·g and K·g·(1 + log₂ n)^k with natural constants K, k chosen with the program, before n and every other input; reason: the standard meaning of the asymptotic notation; 1 + log₂ n instead of log₂ n only matters at n = 1, where the printed polylogarithmic factor is 0
--   - encoding: n^{o(1)} factors → n^{f(n)} for one function f : ℕ → ℝ with f(n) → 0, chosen with the program before n and every other input; reason: the standard meaning of n^{o(1)}; one f serves all occurrences since the bounds are monotone in f
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 78, Theorem C.1

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_EdgeColoring

open DynBrooks Filter Topology

namespace DynMaxMatchEC.Main

/-- **Theorem C.1** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 78). There are a
program, a word-size constant `a`, constants `K, k` and `f → 0` such that for all `n`, all
`0 < p ≤ 1/2` (given as `L = ⌈log₂(1/p)⌉`), all integers `1 < x ≤ z ≤ n` with
`x ≥ √z·2^{50√(log₂ n)}`, every initial graph `G₀` of maximum degree at most `z` with `m₀` edges
(given as the words `n, x, z, L`, `m₀` and an edge list) and every adaptive strategy whose updates
keep every degree at most `z`: on every tape, preprocessing completes within
`K·n·(1 + log₂ n)^k + K·m₀·n^{f(n)}` steps, every delivered update ends within
`K·(z/x)·n^{f(n)}·log₂(1/p)` steps having written at most `K·z·n^{f(n)}/x` color records, and
after preprocessing and every completed update the reported coloring is a proper
`(z + x)`-edge-coloring of the current graph; and for every `t ≥ 1` the probability that update
`t` ends in FAIL is at most `p`. -/
theorem theorem_C_1 :
    ∃ (P : Program) (a K k : ℕ) (f : ℕ → ℝ), Tendsto f atTop (𝓝 0) ∧
      ∀ (n x z : ℕ) (p : ℝ), 0 < p → p ≤ 1 / 2 → 1 < x → x ≤ z → z ≤ n →
        Real.sqrt z * (2 : ℝ) ^ (50 * Real.sqrt (Real.logb 2 n)) ≤ x →
        ∀ (G₀ : SimpleGraph (Fin n)), MaxDegLE z G₀ →
        ∀ (es : List (Fin n × Fin n)), IsEdgeList G₀ es →
        ∀ A : Strategy (wordSize a (n * n + logInv p)) n,
          ((∀ ω : ℕ → BitVec (wordSize a (n * n + logInv p)),
              (Setup.mk P ([n, x, z, logInv p] ++ edgeWords es) G₀ (IsDegLegal z) A).PreprocWithin ω
                  ((K : ℝ) * n * (1 + Real.logb 2 n) ^ k + K * es.length * (n : ℝ) ^ f n) ∧
              (Setup.mk P ([n, x, z, logInv p] ++ edgeWords es) G₀ (IsDegLegal z) A).UpdatesEndWithin ω
                  ((K : ℝ) * ((z : ℝ) / x) * (n : ℝ) ^ f n * Real.logb 2 (1 / p)) ∧
              (Setup.mk P ([n, x, z, logInv p] ++ edgeWords es) G₀ (IsDegLegal z) A).RecordsWithin ω
                  ((K : ℝ) * z * (n : ℝ) ^ f n / x) ∧
              (Setup.mk P ([n, x, z, logInv p] ++ edgeWords es) G₀ (IsDegLegal z) A).AlwaysHolds ω
                  (ColoringOK ((z : ℝ) + x))) ∧
            ∀ t : ℕ, 1 ≤ t →
              coinMeasure (wordSize a (n * n + logInv p))
                  {ω | (Setup.mk P ([n, x, z, logInv p] ++ edgeWords es) G₀ (IsDegLegal z) A).FailsAt
                    ω t} ≤ ENNReal.ofReal p) := by sorry

end DynMaxMatchEC.Main
