-- Prove2me | Theorems.Thm_DynBrooks_lemma_4_24
-- name    : DynBrooks.lemma_4_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:08:23.531195+00:00
-- url     : https://prove2.me/theorems/7fa1912a-ca50-4fee-8195-7d2715730214
-- title:
--   Lemma 4.24 — amplifying cumulative work by independent copies
-- statement:
--   Fix an oblivious sequence of $T=n^{O(1)}$ updates. Suppose a dynamic algorithm is always correct, uses polynomial space, and answers queries in $O(1)$ time without changing its state. Let $W(t)$ be its work through update $t$, including preprocessing, and suppose $E\,W(t)\le F(t)$ with $F(t)\ge t+1$ for $0\le t\le T$. For every fixed $a>0$, independent copies give a polynomial-space algorithm with the same query bound and cumulative work $O(F(t)\log n)$ simultaneously for all prefixes with probability at least $1-n^{-a}$. The bound also holds in expectation for each prefix, and the algorithm remains always correct.
--
--   Precisely: for all $d,a>0,C_0,c_0,W_0$ and every program $P$ there are a program $P'$ and constants $C,c_1,W_1$ such that, whenever $P$ satisfies the hypotheses (with query constant $C_0$, space $C_0n^{c_0}$, and $E\,W_P(t)\le F(t)$ at every word size $w\ge W_0(\lceil\log_2n\rceil+1)$) on an instance and a sequence of length $T\le n^d$, then at every word size $w\ge W_1(\lceil\log_2n\rceil+1)$: $P\{\exists t\le T: W_{P'}(t)>C\,F(t)\log n\}\le n^{-a}$, $E\,W_{P'}(t)\le C\,F(t)\log n$ for each $t\le T$, and every reachable state of $P'$ serves its graph with query constant $C$ and has written at most $Cn^{c_1}$ cells.
--
--   Differences from the source:
--   - reading: 'a dynamic algorithm' that is 'always correct' and 'answers queries' → a program for the problem of §3: legal updates of Brooks graphs, color queries, correctness = Serves; reason: §3 fixes this model for the whole paper, and the lemma is applied to it in the proof of Theorem 1.1(1)
--   - generalization: 3 ≤ ∆ < n (§3), an algorithm maintaining the coloring under the update sequence → n ≥ 2 and every ∆ ≥ 3, ∆ ≥ n included; an arbitrary initial Brooks graph G₀ with an arbitrary edge listing; reason: §3's range and the empty initial graph are special cases; the copies argument does not use them
--   - encoding: the word-RAM model, with no instruction set listed → the word-RAM of DynBrooks.Machine with the standard instruction set, unit-cost coin words and reads that block; reason: with polynomial preprocessing any O(1)-operand word operation can be tabulated, so the choice among standard instruction sets moves only constants
--   - encoding: edge insertions, deletions and color queries → operations delivered as words (0 u v, 1 u v, 2 v) to a completed state; vertices 0,…,n−1; reason: a representation of the operations; the machine still sees one operation at a time
--   - encoding: O(log n)-bit words → every word size w ≥ W₀(⌈log₂ n⌉ + 1), with the program fixed before n, ∆ and w; reason: this is O(log n) bits, it includes the threshold width itself, and it excludes unit-cost big-number arithmetic
--   - reading: answer color queries in O(1) time → from every reachable completed state, on every tape, the query for v completes within C steps, leaves program counter, memory and coin cursor unchanged, and outputs color_s(v); reason: Lemma 4.24 'answers queries in O(1) time without changing its state', §4.8.3 and p.63 'Queries read the color array'
--   - reading: the same query bound → queries in at most C steps for a constant C chosen with P′; reason: O(1) is the query bound; simulating a copy's query costs a constant factor
--   - encoding: a dynamic algorithm and its polynomial space and O(1) queries → a program P whose hypotheses hold at every word size above the threshold, with explicit constants C₀, c₀ quantified before P′; reason: this is how the mission's other items deliver an algorithm (expected_work_4_8_2)
--   - encoding: independent copies give an algorithm → one program P′ of the same machine, chosen before n, running at every word size w ≥ W₁(⌈log₂ n⌉ + 1); reason: its coins and steps are then the real ones
--   - reading: maintain a proper ∆-coloring → every reachable completed state serves a proper {1,…,∆}-coloring of its current graph; completion with probability one on σ follows from the finite expected work; reason: Lemma 4.24 'remains always correct', 'finite expected work ensures termination with probability one'
--   - encoding: for every fixed a > 0 → for every fixed natural a > 0, with P′ and C chosen after a; reason: the proof's q copies depend on a; since n ≥ 2, a natural exponent implies every smaller real one
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Lemma 4.24, p.54 (PDF 56)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol

open MeasureTheory ENNReal

namespace DynBrooks

/-- **Lemma 4.24** (Amplifying cumulative work; Mishra, Mukherjee, *Fully Dynamic Brooks Coloring*,
STOC 2027 submission, sha256 6542a9f1…, p.54 (PDF 56)). Fix an oblivious sequence of `T = n^{O(1)}`
updates. Suppose a dynamic algorithm is always correct, uses polynomial space, and answers queries in
`O(1)` time without changing its state. Let `W(t)` be its work through update `t`, including
preprocessing, and suppose `E W(t) ≤ F(t)` with `F(t) ≥ t + 1` for `0 ≤ t ≤ T`. For every fixed `a > 0`,
independent copies give a polynomial-space algorithm with the same query bound and cumulative work
`O(F(t) log n)` simultaneously for all prefixes with probability at least `1 − n^{−a}`. The bound also
holds in expectation for each prefix, and the algorithm remains always correct.

**Formalization Note.** The given algorithm is a program `P` of the word-RAM whose hypotheses hold at every
word size `w ≥ W₀(⌈log₂ n⌉ + 1)`, with query constant `C₀` and space `|written| ≤ C₀ n^{c₀}` at reachable
states (`Serves` includes "always correct" and "queries in `O(1)` time without changing its state"). The
new algorithm is one program `P'` of the same machine (it runs the copies itself, so its coins and steps
are the real ones), chosen from `P`, `d`, `a`, `C₀`, `c₀`, `W₀` only, and works at every word size
`w ≥ W₁(⌈log₂ n⌉ + 1)`. Its query bound is `O(1)` with a constant `C` (reading of "the same query bound").
The hypotheses and conclusions are for the fixed instance `G₀`, edge listing, oblivious sequence `σ` with
`T = |σ| ≤ n^d`, and bound `F`; correctness and space are over all reachable states. -/
theorem lemma_4_24 :
    ∀ d a : ℕ, 0 < a → ∀ C₀ c₀ W₀ : ℕ, ∀ P : Program, ∃ C c₁ W₁ : ℕ, ∃ P' : Program,
      ∀ n : ℕ, 2 ≤ n → ∀ Δ : ℕ, 3 ≤ Δ →
      ∀ G₀ : SimpleGraph (Fin n), IsBrooks Δ G₀ →
      ∀ es : List (Fin n × Fin n), IsEdgeListing G₀ es →
      ∀ σ : List (Update n), IsLegalSeq Δ G₀ σ → σ.length ≤ n ^ d →
      ∀ F : ℕ → ℝ, (∀ t ≤ σ.length, (t : ℝ) + 1 ≤ F t) →
        (∀ w : ℕ, W₀ * (Nat.clog 2 n + 1) ≤ w →
          (∀ (s : Config w) (G : SimpleGraph (Fin n)), Reach P Δ es G₀ s G →
            Serves P C₀ Δ s G ∧ s.written.card ≤ C₀ * n ^ c₀) ∧
          ∀ t ≤ σ.length,
            ∫⁻ ω, ((Work P Δ es σ ω t : ℕ∞) : ℝ≥0∞) ∂coinMeasure w ≤ ENNReal.ofReal (F t)) →
        ∀ w : ℕ, W₁ * (Nat.clog 2 n + 1) ≤ w →
          coinMeasure w {ω | ∃ t ≤ σ.length,
              ENNReal.ofReal ((C : ℝ) * F t * Real.log n) <
                ((Work P' Δ es σ ω t : ℕ∞) : ℝ≥0∞)} ≤
            ENNReal.ofReal ((n : ℝ) ^ (-(a : ℝ))) ∧
          (∀ t ≤ σ.length,
            ∫⁻ ω, ((Work P' Δ es σ ω t : ℕ∞) : ℝ≥0∞) ∂coinMeasure w ≤
              ENNReal.ofReal ((C : ℝ) * F t * Real.log n)) ∧
          ∀ (s : Config w) (G : SimpleGraph (Fin n)), Reach P' Δ es G₀ s G →
            Serves P' C Δ s G ∧ s.written.card ≤ C * n ^ c₁ := by sorry

end DynBrooks
