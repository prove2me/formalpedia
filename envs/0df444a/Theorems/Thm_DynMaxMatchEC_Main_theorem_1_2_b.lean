-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_theorem_1_2_b
-- name    : DynMaxMatchEC.Main.theorem_1_2_b
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:03:23.545063+00:00
-- url     : https://prove2.me/theorems/86b8ce33-3b16-43f5-83ee-41d9304be992
-- title:
--   Theorem 1.2(b) — randomized (1 + ε)∆-edge-coloring against an adaptive adversary with update time n^{o(1)} log(1/p)/ε and recourse n^{o(1)}/ε when ∆ ≥ 2^{c₀√log n}/ε²
-- statement:
--   There is a constant $c_0>0$ such that the following holds. There is a randomized algorithm that receives an $n$-vertex graph $G$ with $m_0$ edges, an integer $0<\Delta\le n$ bounding the maximum degree at all times under updates chosen by an adaptive adversary, and parameters $0<\varepsilon<1$ and $0<p\le1/2$ with
--   $$\Delta\ge\frac{2^{c_0\sqrt{\log_2 n}}}{\varepsilon^2},$$
--   and maintains a $(1+\varepsilon)\Delta$-edge-coloring of $G$ with per-update failure probability $p$, initialization time $\tilde O(n)+O(m_0n^{o(1)})$, worst-case update time $n^{o(1)}\log(1/p)/\varepsilon$ and recourse $n^{o(1)}/\varepsilon$, outputting after every update all edges whose colors changed with their new colors and the color of an inserted edge. In §3.2 it colors the sparsifier $G'$ with $\Delta=z$, $\varepsilon=x/z$ for the randomized matching algorithm.
--
--   Differences from the source:
--   - reading: the same guarantees as (a) except that its worst-case update time is n^{o(1)}·log(1/p)/ϵ, recourse is n^{o(1)}/ϵ, and the degree requirement is ∆ ≥ 2^{c0√log n}/ϵ² → a proper (1 + ε)∆-edge-coloring, per-update failure probability p, initialization Õ(n) + O(m₀·n^{o(1)}), the output convention, update time n^{f(n)}·log₂(1/p)/ε and n^{f(n)}/ε records, under ∆ ≥ 2^{c₀√(log₂ n)}/ε²; reason: the clause refers to clause (a); its guarantees are spelled out
--   - encoding: c₀ > 0 is some fixed constant → ∃ c₀ > 0 before the program and every input; reason: a fixed constant
--   - encoding: an algorithm (no machine model named; word-RAM data structures with O(log n)-bit words) → a program of the published word RAM DynBrooks_Machine (unit-cost uniform random words, blocking read, write, halt, one step per instruction) with word size a·⌈log₂(n² + L + 1)⌉, the constant a chosen with the program; reason: the paper's data structures (search trees, heaps, arrays) are word-RAM structures; unbounded words would trivialize the bounds
--   - encoding: input: an n-vertex graph with m₀ initial edges and the parameters → the words n, ∆, ⌊ε∆⌋, L = ⌈log₂(1/p)⌉, m₀ and an edge list of G₀ in any order and orientation; reason: machine input
--   - encoding: the input parameter 0 < ε < 1 → the input word ⌊ε∆⌋ (the number of extra colors); the bounds are stated with the real ε; reason: a real number is not a machine word; the program gets less information than ε, so the statement is at least as strong
--   - encoding: the parameter 0 < p ≤ 1/2 → the input word L = ⌈log₂(1/p)⌉; the bounds are stated with the real p; reason: a real number is not a machine word; the program gets less information than p, so the statement is at least as strong
--   - encoding: the maximum vertex degree is at most ∆ at all times → G₀ has maximum degree at most ∆, and an update after which some degree exceeds ∆ is illegal and ends the interaction; reason: the guarantee is required only on legal sequences
--   - encoding: online updates chosen by an adaptive adversary (updates may depend on the algorithm's prior decisions and internal state) → for every deterministic strategy mapping the list of completed configurations (memory, program counter, output, coin cursor; never the unread coins) to the next update or to stop; a proposal that is not legal for the current graph ends the interaction; reason: a randomized adversary is a mixture of deterministic ones whose coins are independent of the algorithm's, so quantifying over deterministic strategies gives the same statement
--   - encoding: the algorithm returns FAIL → the program executes halt while processing an update; the interaction then stops; reason: a halted configuration never reaches a completed state again
--   - encoding: per-update failure probability p: for all t, the probability of returning FAIL while processing the t-th update is at most p → for every t ≥ 1, coinMeasure of {ω : update t is delivered and its processing executes halt} ≤ p, and every other guarantee holds on every coin tape; reason: the definition on p. 2; the measure is applied to the event as a set (outer measure), which is at least as strong
--   - encoding: a (1 + ϵ)∆-edge-coloring → colors are natural numbers c with 1 ≤ c ≤ (1 + ε)∆, i.e. at most ⌊(1 + ε)∆⌋ colors; reason: colors are integers
--   - encoding: maintains a (1 + ε)∆-edge-coloring and outputs, after every update, all edges whose colors changed with their new colors and the color of a newly inserted edge → the coloring is the uncolored assignment with every output record u, v, c applied in order; after preprocessing and after every completed update it is a proper (1 + ε)∆-edge-coloring of the current graph; reason: the coloring is read from the log, so every color change must be written; the color of an inserted edge is the last color written for that pair, so the log states it (an edge re-inserted after a deletion keeps the color last written for it unless a new record is written, and that color must then be proper); the initial coloring of G₀ is written in preprocessing
--   - encoding: recourse: the number of edges whose color may change after an update → the number of color records written while processing the update; reason: every change must be written as a record; the algorithm writes its changes and the new edge's color, which the constants absorb
--   - encoding: initialization time → preprocessing (the run from the start configuration with the input words pending) reaches a completed state within the bound on every coin tape; reason: a completed state is the machine blocked at read waiting for the first update
--   - encoding: worst-case update time and recourse → every delivered update's processing ends within the bound, and writes at most the stated number of records, on every coin tape; reason: worst-case means every update of every run, not an average
--   - encoding: O(·) and Õ(·) bounds → K·g and K·g·(1 + log₂ n)^k with natural constants K, k chosen with the program, before n and every other input; reason: the standard meaning of the asymptotic notation; 1 + log₂ n instead of log₂ n only matters at n = 1, where the printed polylogarithmic factor is 0
--   - encoding: n^{o(1)} factors → n^{f(n)} for one function f : ℕ → ℝ with f(n) → 0, chosen with the program before n and every other input; reason: the standard meaning of n^{o(1)}; one f serves all occurrences since the bounds are monotone in f
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 4, Theorem 1.2(b)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model
import Definitions.Def_DynMaxMatchEC_Main_EdgeColoring

open DynBrooks Filter Topology

namespace DynMaxMatchEC.Main

/-- **Theorem 1.2(b)** (Chuzhoy, manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 4). There is a
constant `c₀ > 0`, and there are a program, a word-size constant `a`, constants `K, k` and `f → 0`,
such that for every `n`, every integer `0 < Δ ≤ n`, all `0 < ε < 1` and `0 < p ≤ 1/2` with
`Δ ≥ 2^{c₀√(log₂ n)}/ε²` (given as the words `n, Δ, ⌊εΔ⌋, ⌈log₂(1/p)⌉`), every initial graph `G₀`
of maximum degree at most `Δ` with `m₀` edges (given as an edge list) and every adaptive strategy
whose updates keep every degree at most `Δ`: on every tape, preprocessing completes within
`K·n·(1 + log₂ n)^k + K·m₀·n^{f(n)}` steps, every delivered update ends within
`n^{f(n)}·log₂(1/p)/ε` steps having written at most `n^{f(n)}/ε` color records, and the reported
coloring is a proper `(1 + ε)Δ`-edge-coloring of the current graph after preprocessing and after every
completed update; and for every `t ≥ 1` the probability that update `t` ends in FAIL is at most
`p`. -/
theorem theorem_1_2_b :
    ∃ c₀ : ℝ, 0 < c₀ ∧
      ∃ (P : Program) (a K k : ℕ) (f : ℕ → ℝ), Tendsto f atTop (𝓝 0) ∧
        ∀ (n Δ : ℕ) (ε p : ℝ), 0 < Δ → Δ ≤ n → 0 < ε → ε < 1 → 0 < p → p ≤ 1 / 2 →
          (2 : ℝ) ^ (c₀ * Real.sqrt (Real.logb 2 n)) / ε ^ 2 ≤ Δ →
          ∀ (G₀ : SimpleGraph (Fin n)), MaxDegLE Δ G₀ →
          ∀ (es : List (Fin n × Fin n)), IsEdgeList G₀ es →
          ∀ A : Strategy (wordSize a (n * n + logInv p)) n,
            ((∀ ω : ℕ → BitVec (wordSize a (n * n + logInv p)),
                (Setup.mk P ([n, Δ, ⌊ε * Δ⌋₊, logInv p] ++ edgeWords es) G₀ (IsDegLegal Δ) A).PreprocWithin
                    ω ((K : ℝ) * n * (1 + Real.logb 2 n) ^ k + K * es.length * (n : ℝ) ^ f n) ∧
                (Setup.mk P ([n, Δ, ⌊ε * Δ⌋₊, logInv p] ++ edgeWords es) G₀ (IsDegLegal Δ) A).UpdatesEndWithin
                    ω ((n : ℝ) ^ f n * Real.logb 2 (1 / p) / ε) ∧
                (Setup.mk P ([n, Δ, ⌊ε * Δ⌋₊, logInv p] ++ edgeWords es) G₀ (IsDegLegal Δ) A).RecordsWithin
                    ω ((n : ℝ) ^ f n / ε) ∧
                (Setup.mk P ([n, Δ, ⌊ε * Δ⌋₊, logInv p] ++ edgeWords es) G₀ (IsDegLegal Δ) A).AlwaysHolds
                    ω (ColoringOK ((1 + ε) * Δ))) ∧
              ∀ t : ℕ, 1 ≤ t →
                coinMeasure (wordSize a (n * n + logInv p))
                    {ω | (Setup.mk P ([n, Δ, ⌊ε * Δ⌋₊, logInv p] ++ edgeWords es) G₀ (IsDegLegal Δ)
                      A).FailsAt ω t} ≤ ENNReal.ofReal p) := by sorry

end DynMaxMatchEC.Main
