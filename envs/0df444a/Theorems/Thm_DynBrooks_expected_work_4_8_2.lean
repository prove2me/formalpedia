-- Prove2me | Theorems.Thm_DynBrooks_expected_work_4_8_2
-- name    : DynBrooks.expected_work_4_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:08:07.151137+00:00
-- url     : https://prove2.me/theorems/452a8efe-29b7-4988-81c0-bc5cc9210337
-- title:
--   §4.8.2 — expected work of the base algorithm: $E\,W(t)\le n^{c'}+t\ell^{k'}$
-- statement:
--   There is a randomized fully dynamic algorithm for Brooks graphs, always correct, with polynomial space and constant-time color queries, such that for suitable constants $c',k'$, over a fixed update sequence of length $T\le n^{d}$, the work $W(t)$ through update $t$, including preprocessing, satisfies
--
--   $$E\,W(t)\le C\bigl(n^{c'}+t\,\ell^{k'}\bigr)\qquad(0\le t\le T),\qquad \ell=\max\{1,\lceil\log(n+T+2)\rceil\},$$
--
--   where $c',k'$ are fixed before $d$, and the program and $C$ may depend on $d$.
--
--   Combined with Lemma 4.24 this proves Theorem 1.1(1).
--
--   Differences from the source:
--   - encoding: the word-RAM model, with no instruction set listed → the word-RAM of DynBrooks.Machine with the standard instruction set, unit-cost coin words and reads that block; reason: with polynomial preprocessing any O(1)-operand word operation can be tabulated, so the choice among standard instruction sets moves only constants
--   - encoding: edge insertions, deletions and color queries → operations delivered as words (0 u v, 1 u v, 2 v) to a completed state; vertices 0,…,n−1; reason: a representation of the operations; the machine still sees one operation at a time
--   - encoding: O(log n)-bit words → every word size w ≥ W₀(⌈log₂ n⌉ + 1), with the program fixed before n, ∆ and w; reason: this is O(log n) bits, it includes the threshold width itself, and it excludes unit-cost big-number arithmetic
--   - generalization: an algorithm maintaining the coloring under the update sequence (initialized from the current graph, §5.3) → preprocessing on an arbitrary initial Brooks graph G₀ given by an arbitrary edge listing; reason: the empty initial graph is a special case
--   - reading: answer color queries in O(1) time → from every reachable completed state, on every tape, the query for v completes within C steps, leaves program counter, memory and coin cursor unchanged, and outputs color_s(v); reason: Lemma 4.24 'answers queries in O(1) time without changing its state', §4.8.3 and p.63 'Queries read the color array'
--   - reading: maintain a proper ∆-coloring → every reachable completed state serves a proper {1,…,∆}-coloring of its current graph; completion with probability one on σ follows from the finite expected work; reason: Lemma 4.24 'remains always correct', 'finite expected work ensures termination with probability one'
--   - encoding: words of space → the number of memory cells written so far, at every reachable completed state; reason: a cell counts once written; cells never written are the initial zero memory
--   - reading: 'for suitable constants c′, k′, EW(t) ≤ n^{c′} + tℓ^{k′}' → ∃ natural c′ k′ before the horizon exponent d, then ∃ C with E W(t) ≤ C(n^{c′} + tℓ^{k′}); reason: c′, k′ independent of d is what Theorem 1.1(1) needs (see R4 there); a leading constant replaces absorbing constants into the exponents
--   - generalization: 'Configure the base algorithm for the full horizon T' → the program is configured from d (horizon n^d) and is not told T ≤ n^d; reason: every T ≤ n^d is covered
--   - encoding: the expectation over the algorithm's randomness → the lower Lebesgue integral of the ℕ∞-valued work under the coin law, σ fixed in advance; reason: an oblivious sequence is fixed before the coins
--   - encoding: 3 ≤ ∆ < n (§3); ∆ ≥ 3 and static recomputation for n < n₀ (p.53) → n ≥ 2 and ∆ ≥ 3, ∆ ≥ n included; reason: for n ≤ 1 there is no legal update; §3 reduces ∆ ≥ n to a fixed coloring; Theorem 1.1 is stated for every ∆ ≥ 3
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), §4.8.2, p.53 (PDF 55); proof of Theorem 1.1(1), p.54 (PDF 56)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol

open MeasureTheory ENNReal

namespace DynBrooks

/-- **§4.8.2, expected work of the base algorithm, and the proof of Theorem 1.1(1)** (Mishra, Mukherjee,
*Fully Dynamic Brooks Coloring*, STOC 2027 submission, sha256 6542a9f1…, pp.53–54 (PDF 55–56)). There is
a randomized fully dynamic algorithm, always correct, with polynomial space and constant-time color
queries (array reads), such that for suitable constants `c', k'`, over a fixed update sequence of
polynomial length `T`, the work through update `t`, including preprocessing, satisfies
`E W(t) ≤ n^{c'} + t ℓ^{k'}` for `0 ≤ t ≤ T`, where `ℓ = max{1, ⌈log(n + T + 2)⌉}` (§3, p.13).

**Formalization Note.** Machine, protocol, `Work`, `Reach` and `Serves` as in `theorem_1_1`; the
expectation is the lower Lebesgue integral of the `ℕ∞`-valued work under the coin law, for the fixed
(oblivious) sequence `σ`, `T = |σ| ≤ n^d`. The exponents `c', k'` are chosen before the horizon exponent
`d`; a leading constant `C` (depending on `d`) replaces absorbing constants into the exponents. The program
is configured for the horizon `n^d` and is not told `T`. Polynomial space is `|written| ≤ C n^{c'}` at every
reachable completed state. -/
theorem expected_work_4_8_2 :
    ∃ c' k' : ℕ, ∀ d : ℕ, ∃ C W₀ : ℕ, ∃ P : Program,
      ∀ n : ℕ, 2 ≤ n → ∀ Δ : ℕ, 3 ≤ Δ → ∀ w : ℕ, W₀ * (Nat.clog 2 n + 1) ≤ w →
      ∀ G₀ : SimpleGraph (Fin n), IsBrooks Δ G₀ →
      ∀ es : List (Fin n × Fin n), IsEdgeListing G₀ es →
        (∀ σ : List (Update n), IsLegalSeq Δ G₀ σ → σ.length ≤ n ^ d → ∀ t ≤ σ.length,
          ∫⁻ ω, ((Work P Δ es σ ω t : ℕ∞) : ℝ≥0∞) ∂coinMeasure w ≤
            ENNReal.ofReal ((C : ℝ) * ((n : ℝ) ^ c' + (t : ℝ) * (ell n σ.length : ℝ) ^ k'))) ∧
        ∀ (s : Config w) (G : SimpleGraph (Fin n)), Reach P Δ es G₀ s G →
          Serves P C Δ s G ∧ s.written.card ≤ C * n ^ c' := by sorry

end DynBrooks
