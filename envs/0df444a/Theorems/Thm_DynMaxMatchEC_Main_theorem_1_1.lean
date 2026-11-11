-- Prove2me | Theorems.Thm_DynMaxMatchEC_Main_theorem_1_1
-- name    : DynMaxMatchEC.Main.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:02:25.325275+00:00
-- url     : https://prove2.me/theorems/3ddaa1ff-257e-4e7e-9fdc-0b04bfc20041
-- title:
--   Theorem 1.1 — fully dynamic maximal matching against an adaptive adversary: randomized n^{1−δ/4+o(1)}·log(1/p) and deterministic n^{20/21+o(1)} worst-case update time, recourse Õ(n^δ) and Õ(n^{4/21})
-- statement:
--   Let $G$ be a graph on $n$ vertices that starts with no edges and then undergoes edge insertions and deletions chosen online by an **adaptive adversary**, who sees every completed configuration of the machine (all prior decisions and internal state) but not the unused random words. After preprocessing and after every update the algorithm must have written to its output every edge added to or deleted from the matching $M^*$ it maintains, and $M^*$ must be a maximal matching of the current graph.
--
--   **(a)** For every constant $0<\delta\le4/5$ there are a program, a word-size constant $a$, constants $K,k$ and a function $f$ with $f(n)\to0$ such that for every $n\ge1$, every $0<p\le1/2$ (given as $L=\lceil\log_2(1/p)\rceil$; words of $a\lceil\log_2(n+L+1)\rceil$ bits) and every strategy of the adversary, on every coin tape: preprocessing finishes within $Kn(1+\log_2n)^k$ steps; every delivered update finishes (with a maximal matching or with FAIL) within
--   $$n^{1-\delta/4+f(n)}\cdot\log_2(1/p)$$
--   steps and writes at most $Kn^{\delta}(1+\log_2n)^k$ change records; $M^*$ is a maximal matching after preprocessing and after every update that did not fail; and for every $t\ge1$, the probability that update $t$ is delivered and fails is at most $p$.
--
--   **(b)** There are a program without random instructions, $a$, $K$, $k$ and $f\to0$ such that for every $n\ge1$ (words of $a\lceil\log_2(n+1)\rceil$ bits) and every strategy: preprocessing finishes within $Kn(1+\log_2n)^k$ steps; every update completes within $n^{20/21+f(n)}$ steps writing at most $Kn^{4/21}(1+\log_2n)^k$ records; and $M^*$ is always a maximal matching.
--
--   These are the first algorithms whose worst-case update time and recourse are both sublinear in $n$, even against an oblivious adversary; they answer the open problem of [BBKS25] for algorithms that report every change.
--
--   Differences from the source:
--   - encoding: an algorithm (no machine model named; word-RAM data structures with O(log n)-bit words) → a program of the published word RAM DynBrooks_Machine (unit-cost uniform random words, blocking read, write, halt, one step per instruction) with word size a·⌈log₂(n + L + 1)⌉ in (a) and a·⌈log₂(n + 1)⌉ in (b), the constant a chosen with the program; reason: the paper's data structures (search trees, heaps, arrays) are word-RAM structures; unbounded words would trivialize the bounds
--   - encoding: the parameter 0 < p ≤ 1/2 → the input word L = ⌈log₂(1/p)⌉; the bounds are stated with the real p; reason: a real number is not a machine word; the program gets less information than p, so the statement is at least as strong
--   - encoding: online updates chosen by an adaptive adversary (updates may depend on the algorithm's prior decisions and internal state) → for every deterministic strategy mapping the list of completed configurations (memory, program counter, output, coin cursor; never the unread coins) to the next update or to stop; a proposal that is not legal for the current graph ends the interaction; reason: a randomized adversary is a mixture of deterministic ones whose coins are independent of the algorithm's, so quantifying over deterministic strategies gives the same statement
--   - encoding: the algorithm returns FAIL → the program executes halt while processing an update; the interaction then stops; reason: a halted configuration never reaches a completed state again
--   - encoding: per-update failure probability p: for all t, the probability of returning FAIL while processing the t-th update is at most p → for every t ≥ 1, coinMeasure of {ω : update t is delivered and its processing executes halt} ≤ p, and every other guarantee holds on every coin tape; reason: the definition on p. 2; the measure is applied to the event as a set (outer measure), which is at least as strong
--   - encoding: output, after every update, all edges added to or deleted from M∗; recourse Õ(·) → M∗ is the empty set with every output record u, v, b applied in order; the recourse bound is on the number of records written while processing the update; reason: every change must be written as a record, so the record count bounds the number of changes; the paper's algorithm writes exactly its changes
--   - encoding: initialization time → preprocessing (the run from the start configuration with the input words pending) reaches a completed state within the bound on every coin tape; reason: a completed state is the machine blocked at read waiting for the first update
--   - encoding: worst-case update time and recourse → every delivered update's processing ends within the bound, and writes at most the stated number of records, on every coin tape; reason: worst-case means every update of every run, not an average
--   - encoding: O(·) and Õ(·) bounds → K·g and K·g·(1 + log₂ n)^k with natural constants K, k chosen with the program, before n and every other input; reason: the standard meaning of the asymptotic notation; 1 + log₂ n instead of log₂ n only matters at n = 1, where the printed polylogarithmic factor is 0
--   - encoding: n^{o(1)} factors → n^{f(n)} for one function f : ℕ → ℝ with f(n) → 0, chosen with the program before n and every other input; reason: the standard meaning of n^{o(1)}; one f serves all occurrences since the bounds are monotone in f
--   - encoding: a deterministic algorithm → a program with no coin instruction, with every guarantee for every coin tape and every update completing (never FAIL); reason: the machine's only source of randomness is the coin instruction
--   - encoding: an n-vertex graph → vertices Fin n with n ≥ 1, starting from the empty graph ⊥; reason: Lean convention
-- source:
--   Chuzhoy, New Algorithms for Dynamic Maximal Matching and Edge Coloring (manuscript, Nov. 1, 2026; PDF sha256 2c277528…4ca5), p. 2, Theorem 1.1

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol
import Definitions.Def_DynMaxMatchEC_Main_Model

open DynBrooks Filter Topology

namespace DynMaxMatchEC.Main

/-- **Theorem 1.1** (Chuzhoy, *New Algorithms for Dynamic Maximal Matching and Edge Coloring*,
manuscript Nov. 1, 2026, PDF sha256 2c277528…4ca5, p. 2). Fully dynamic maximal matching from the
empty graph on `Fin n` against an adaptive adversary that sees every completed configuration, with
every change to `M∗` written to the output as a record `u, v, b`.

(a) For every constant `0 < δ ≤ 4/5` there are a program, a word-size constant `a`, constants
`K, k` and `f → 0` such that for all `n ≥ 1`, all `0 < p ≤ 1/2` (given as the word
`L = ⌈log₂(1/p)⌉`; word size `a·⌈log₂(n + L + 1)⌉`) and every strategy: on every coin tape,
preprocessing completes within `K·n·(1 + log₂ n)^k` steps, every delivered update ends (completed or
FAIL) within `n^{1−δ/4+f(n)}·log₂(1/p)` steps having written at most `K·n^δ·(1 + log₂ n)^k`
records, and the reported matching is a maximal matching of the current graph after preprocessing
and after every completed update; and for every `t ≥ 1` the probability that update `t` is delivered
and ends in FAIL is at most `p`.

(b) There are a coin-free program, `a`, `K`, `k` and `f → 0` such that for all `n ≥ 1` (word size
`a·⌈log₂(n + 1)⌉`), every strategy and every tape: preprocessing completes within
`K·n·(1 + log₂ n)^k` steps, every delivered update completes within `n^{20/21+f(n)}` steps having
written at most `K·n^{4/21}·(1 + log₂ n)^k` records, and the reported matching is always a maximal
matching of the current graph. -/
theorem theorem_1_1 :
    (∀ δ : ℝ, 0 < δ → δ ≤ 4 / 5 →
      ∃ (P : Program) (a K k : ℕ) (f : ℕ → ℝ), Tendsto f atTop (𝓝 0) ∧
        ∀ n : ℕ, 1 ≤ n → ∀ p : ℝ, 0 < p → p ≤ 1 / 2 →
          ∀ A : Strategy (wordSize a (n + logInv p)) n,
            ((∀ ω : ℕ → BitVec (wordSize a (n + logInv p)),
                (Setup.mk P [n, logInv p] ⊥ IsEdgeUpdate A).PreprocWithin ω
                    ((K : ℝ) * n * (1 + Real.logb 2 n) ^ k) ∧
                (Setup.mk P [n, logInv p] ⊥ IsEdgeUpdate A).UpdatesEndWithin ω
                    ((n : ℝ) ^ (1 - δ / 4 + f n) * Real.logb 2 (1 / p)) ∧
                (Setup.mk P [n, logInv p] ⊥ IsEdgeUpdate A).RecordsWithin ω
                    ((K : ℝ) * (n : ℝ) ^ δ * (1 + Real.logb 2 n) ^ k) ∧
                (Setup.mk P [n, logInv p] ⊥ IsEdgeUpdate A).AlwaysHolds ω
                    fun G out => IsMaximalMatching G (reportedMatching n out)) ∧
              ∀ t : ℕ, 1 ≤ t →
                coinMeasure (wordSize a (n + logInv p))
                    {ω | (Setup.mk P [n, logInv p] ⊥ IsEdgeUpdate A).FailsAt ω t} ≤
                  ENNReal.ofReal p)) ∧
    (∃ (P : Program) (a K k : ℕ) (f : ℕ → ℝ), CoinFree P ∧ Tendsto f atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → ∀ (A : Strategy (wordSize a n) n) (ω : ℕ → BitVec (wordSize a n)),
        (Setup.mk P [n] ⊥ IsEdgeUpdate A).PreprocWithin ω
            ((K : ℝ) * n * (1 + Real.logb 2 n) ^ k) ∧
        (Setup.mk P [n] ⊥ IsEdgeUpdate A).UpdatesCompleteWithin ω
            ((n : ℝ) ^ ((20 : ℝ) / 21 + f n)) ∧
        (Setup.mk P [n] ⊥ IsEdgeUpdate A).RecordsWithin ω
            ((K : ℝ) * (n : ℝ) ^ ((4 : ℝ) / 21) * (1 + Real.logb 2 n) ^ k) ∧
        (Setup.mk P [n] ⊥ IsEdgeUpdate A).AlwaysHolds ω
            fun G out => IsMaximalMatching G (reportedMatching n out)) := by sorry

end DynMaxMatchEC.Main
