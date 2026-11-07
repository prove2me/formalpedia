-- Prove2me | Theorems.Thm_DynBrooks_theorem_1_1
-- name    : DynBrooks.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:08:02.82347+00:00
-- url     : https://prove2.me/theorems/e4797025-3da6-4831-b98e-56e5fb5e3381
-- title:
--   Theorem 1.1 — fully dynamic Brooks coloring: polylog amortized (oblivious) and $O(\Delta\log_\Delta n)$ (adaptive) update time
-- statement:
--   Let $\Delta\ge3$ be an integer. There are randomized fully dynamic algorithms that maintain a proper $\Delta$-coloring of an $n$-vertex graph under edge insertions and deletions, provided that throughout the update sequence the graph has maximum degree at most $\Delta$ and contains no $K_{\Delta+1}$. Both algorithms answer color queries in $O(1)$ time and satisfy the following respective guarantees:
--
--   1. **Oblivious adversary.** There is an algorithm with polylogarithmic amortized update time with high probability, after an additive polynomial initialization cost: for any prescribed polynomial-length update sequence, with high probability the total work through the first $t$ updates, including preprocessing, is $O(n^c+t\log^kn)$ simultaneously for every prefix length $t$, for some constants $c,k>0$.
--   2. **Adaptive adversary.** There is an algorithm with $O(\Delta\log_\Delta n)$ update time with high probability, for each individual update.
--
--   Precisely, in the word-RAM of the mission:
--
--   1. there are $c,k$ such that for every horizon exponent $d$ and confidence exponent $a>0$ there are a program $P$ and constants $C,W_0$ such that for all $n\ge2$, $\Delta\ge3$, word sizes $w\ge W_0(\lceil\log_2n\rceil+1)$, initial Brooks graphs $G_0$ and edge listings: for every legal update sequence $\sigma$ of length $T\le n^d$,
--   $$P_\omega\bigl[\exists\,t\le T:\ W(t)>C(n^c+t\log^kn)\bigr]\le n^{-a},$$
--   every update of $\sigma$ completes with probability one, and every reachable completed state serves its current graph with query constant $C$;
--   2. there is $c'$ such that for every $c>0$ there are $P,C,W_0$ such that, in the same range, preprocessing takes at most $Cn^{c'}$ steps on every tape, every reachable completed state serves its graph with query constant $C$, and from every reachable completed state and every legal next update, under fresh coins, the update takes more than $C\Delta\log n/\log\Delta$ steps with probability at most $n^{-c}$ and completes with probability one.
--
--   Differences from the source:
--   - encoding: the word-RAM model, with no instruction set listed → the word-RAM of DynBrooks.Machine with the standard instruction set, unit-cost coin words and reads that block; reason: with polynomial preprocessing any O(1)-operand word operation can be tabulated, so the choice among standard instruction sets moves only constants
--   - encoding: edge insertions, deletions and color queries → operations delivered as words (0 u v, 1 u v, 2 v) to a completed state; vertices 0,…,n−1; reason: a representation of the operations; the machine still sees one operation at a time
--   - encoding: O(log n)-bit words → every word size w ≥ W₀(⌈log₂ n⌉ + 1), with the program fixed before n, ∆ and w; reason: this is O(log n) bits, it includes the threshold width itself, and it excludes unit-cost big-number arithmetic
--   - reading: 'for any prescribed polynomial-length update sequence … O(n^c + t log^k n) … for some constants c, k > 0' → ∃ c k before the horizon exponent d (T ≤ n^d) and the confidence exponent a; only C, W₀ and the program depend on d and a; reason: with c after d the clause would be trivial (static recomputation after each update costs O(n^{d+2}) in total); §4.8.2 gives c′, k′ independent of d
--   - generalization: an algorithm maintaining the coloring under the update sequence (initialized from the current graph, §5.3) → preprocessing on an arbitrary initial Brooks graph G₀ given by an arbitrary edge listing; reason: the empty initial graph is a special case
--   - reading: answer color queries in O(1) time → from every reachable completed state, on every tape, the query for v completes within C steps, leaves program counter, memory and coin cursor unchanged, and outputs color_s(v); reason: Lemma 4.24 'answers queries in O(1) time without changing its state', §4.8.3 and p.63 'Queries read the color array'
--   - generalization: 'Configure the base algorithm for the full horizon T' → the program depends on d and is not told T ≤ n^d; reason: every T ≤ n^d is covered
--   - reading: with high probability: 1 − n^{−c} for suitable constant c (§3) → for every fixed natural exponent, with the program and constants chosen after the exponent; reason: the proofs give every exponent: Lemma 4.24 'for every fixed a > 0', Corollary 6.3 'For every fixed c > 0'; the algorithm depends on the exponent (q copies; L in §5.4); since n ≥ 2, a natural exponent implies every smaller real one
--   - encoding: an adaptive adversary, which chooses each update from the previously completed states but not the fresh randomness → every reachable completed state and every legal next update, with probability over fresh coins; reason: the paper's own form, p.63: 'Both time guarantees hold after fixing the preceding history and the next update'; it implies the bound against every such adversary
--   - reading: maintain a proper ∆-coloring → every reachable completed state serves a proper {1,…,∆}-coloring of its current graph, and every update completes with probability one; reason: Corollary 6.3 'always maintains', 'terminates with probability one'; Lemma 4.24 'remains always correct'
--   - encoding: n-vertex graphs, natural logarithms, log_∆ n → n ≥ 2, Real.log, log_∆ n = log n / log ∆; reason: for n ≤ 1 there is no legal update; with ∆ ≥ 3 and n ≥ 2 both logarithms are positive; ∆ ≥ n is included
--   - reading: clause (2) is silent about preprocessing → preprocessing takes at most Cn^{c′} steps on every tape; reason: §3 allows polynomial preprocessing and Corollary 6.3 states it; the static Brooks start (Theorem 5.7) and the BFS start (p.70) are deterministic
--   - encoding: the probability over the algorithm's random choices; the work through the first t updates → the coin law; Work counts every step from the start of preprocessing to the completed state after update t (∞ if some update never completes); σ fixed before the coins; reason: an oblivious sequence is fixed independently of the coins
--   - encoding: constants c, k > 0 → natural numbers c, k, and c′ in clause (2); reason: for n ≥ 2 a larger exponent only weakens the bound up to the leading constant C, so natural exponents lose nothing
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Theorem 1.1, p.2 (PDF 4); model §3, p.13 (PDF 15)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol

open MeasureTheory ENNReal

namespace DynBrooks

/-- **Theorem 1.1** (Mishra, Mukherjee, *Fully Dynamic Brooks Coloring*, STOC 2027 submission,
sha256 6542a9f1…, p.2 (PDF 4)). Let `∆ ≥ 3`. There are randomized fully dynamic algorithms that
maintain a proper `∆`-coloring of an `n`-vertex graph under edge insertions and deletions, provided
that throughout the update sequence the graph has maximum degree at most `∆` and contains no
`K_{∆+1}`. Both answer color queries in `O(1)` time, and:

1. (oblivious adversary) for any prescribed polynomial-length update sequence, with high probability
   the total work through the first `t` updates, including preprocessing, is `O(n^c + t log^k n)`
   simultaneously for every prefix length `t`, for some constants `c, k > 0`;
2. (adaptive adversary) each individual update takes `O(∆ log_∆ n)` time with high probability.

**Formalization Note.**
* Machine (R1): the word-RAM of `DynBrooks.Machine`, with unit-cost coins and a `read` that blocks
  until an operation is delivered; every executed instruction is one step. A program is fixed before
  `n`, `∆` and the word size `w`, and "O(log n)-bit words" is every `w ≥ W₀(⌈log₂ n⌉ + 1)` (R3).
* Protocol (R2, R5): preprocessing receives `n`, `min ∆ n` and an arbitrary edge listing of an arbitrary
  initial Brooks graph `G₀` (the empty graph is a special case); updates and queries arrive as words.
* Clause (1) quantifier order (R4): `c, k` come before the horizon exponent `d` and the confidence
  exponent `a`; only `C`, `W₀` and the program depend on `d` and `a` (R7, R8). The program is not told
  the horizon `T = |σ| ≤ n^d`. `Work … t` counts every step from the start of preprocessing to the
  completed state after update `t`; it is `⊤` if some update never completes. The event "some prefix
  exceeds its bound" is one event, under the coin law, with `σ` fixed in advance (oblivious).
* Clause (2) (R9, R12): from every reachable completed state, and every legal next update, on fresh
  coins; preprocessing is polynomial on every tape. `log` is the natural logarithm and
  `log_∆ n = log n / log ∆`.
* Both clauses (R6, R10): every reachable completed state `Serves` its current graph — `query v`
  takes at most `C` steps on every tape, changes no state, and outputs a color in `{1, …, ∆}`, and
  these colors form a proper coloring; every update completes with probability one. -/
theorem theorem_1_1 :
    (∃ c k : ℕ, ∀ d a : ℕ, 0 < a → ∃ C W₀ : ℕ, ∃ P : Program,
      ∀ n : ℕ, 2 ≤ n → ∀ Δ : ℕ, 3 ≤ Δ → ∀ w : ℕ, W₀ * (Nat.clog 2 n + 1) ≤ w →
      ∀ G₀ : SimpleGraph (Fin n), IsBrooks Δ G₀ →
      ∀ es : List (Fin n × Fin n), IsEdgeListing G₀ es →
        (∀ σ : List (Update n), IsLegalSeq Δ G₀ σ → σ.length ≤ n ^ d →
          coinMeasure w {ω | ∃ t ≤ σ.length,
              ENNReal.ofReal ((C : ℝ) * ((n : ℝ) ^ c + (t : ℝ) * Real.log n ^ k)) <
                ((Work P Δ es σ ω t : ℕ∞) : ℝ≥0∞)} ≤
            ENNReal.ofReal ((n : ℝ) ^ (-(a : ℝ))) ∧
          coinMeasure w {ω | Work P Δ es σ ω σ.length = ⊤} = 0) ∧
        ∀ (s : Config w) (G : SimpleGraph (Fin n)), Reach P Δ es G₀ s G → Serves P C Δ s G) ∧
    (∃ c' : ℕ, ∀ c : ℕ, 0 < c → ∃ C W₀ : ℕ, ∃ P : Program,
      ∀ n : ℕ, 2 ≤ n → ∀ Δ : ℕ, 3 ≤ Δ → ∀ w : ℕ, W₀ * (Nat.clog 2 n + 1) ≤ w →
      ∀ G₀ : SimpleGraph (Fin n), IsBrooks Δ G₀ →
      ∀ es : List (Fin n × Fin n), IsEdgeListing G₀ es →
        (∀ ω : ℕ → BitVec w, time P ω (startConfig w Δ es) ≤ ((C * n ^ c' : ℕ) : ℕ∞)) ∧
        ∀ (s : Config w) (G : SimpleGraph (Fin n)), Reach P Δ es G₀ s G →
          Serves P C Δ s G ∧
          ∀ x : Update n, IsLegal Δ G x →
            coinMeasure w {ω | ENNReal.ofReal ((C : ℝ) * Δ * (Real.log n / Real.log Δ)) <
                ((time P ω (feed s x.words) : ℕ∞) : ℝ≥0∞)} ≤
              ENNReal.ofReal ((n : ℝ) ^ (-(c : ℝ))) ∧
            coinMeasure w {ω | time P ω (feed s x.words) = ⊤} = 0) := by sorry

end DynBrooks
