-- Prove2me | Theorems.Thm_DynBrooks_theorem_5_7
-- name    : DynBrooks.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:07:54.171581+00:00
-- url     : https://prove2.me/theorems/b89f057b-9734-49f7-b293-c200d385432e
-- title:
--   Theorem 5.7 — the direct branch: $O(\Delta\log_\Delta n)$ adaptive update time for $16\le\Delta<n$
-- statement:
--   Fix $16\le\Delta<n$. There is a randomized fully dynamic algorithm for graphs on $[n]$ of maximum degree at most $\Delta$ with no $K_{\Delta+1}$ that always maintains an explicit proper $[\Delta]$-coloring against an adaptive adversary. Each update takes $O(\Delta\log_\Delta n)$ time in expectation and with high probability, and a color query takes $O(1)$ time. Both time guarantees hold after fixing the preceding history and the next update. The algorithm uses $O(n^2)$ words of space and polynomial preprocessing, and changes the colors of at most $O(\log_\Delta n)$ vertices between consecutive completed states.
--
--   Precisely: there is $c'$ such that for every $c>0$ there are a program and constants $C,W_0$ such that, for all $16\le\Delta<n$, word sizes $w\ge W_0(\lceil\log_2n\rceil+1)$, initial Brooks graphs and edge listings: preprocessing takes at most $Cn^{c'}$ steps on every tape; every reachable completed state serves its graph with query constant $C$ and has written at most $Cn^2$ cells; and for every legal next update, under fresh coins, the expected time is at most $C\Delta\log n/\log\Delta$, the time exceeds this bound with probability at most $n^{-c}$, the update completes with probability one, and at most $C\log n/\log\Delta$ vertices change color.
--
--   Differences from the source:
--   - encoding: the word-RAM model, with no instruction set listed → the word-RAM of DynBrooks.Machine with the standard instruction set, unit-cost coin words and reads that block; reason: with polynomial preprocessing any O(1)-operand word operation can be tabulated, so the choice among standard instruction sets moves only constants
--   - encoding: edge insertions, deletions and color queries → operations delivered as words (0 u v, 1 u v, 2 v) to a completed state; vertices 0,…,n−1; reason: a representation of the operations; the machine still sees one operation at a time
--   - encoding: O(log n)-bit words → every word size w ≥ W₀(⌈log₂ n⌉ + 1), with the program fixed before n, ∆ and w; reason: this is O(log n) bits, it includes the threshold width itself, and it excludes unit-cost big-number arithmetic
--   - generalization: an algorithm maintaining the coloring under the update sequence (initialized from the current graph, §5.3) → preprocessing on an arbitrary initial Brooks graph G₀ given by an arbitrary edge listing; reason: the empty initial graph is a special case
--   - reading: answer color queries in O(1) time → from every reachable completed state, on every tape, the query for v completes within C steps, leaves program counter, memory and coin cursor unchanged, and outputs color_s(v); reason: Lemma 4.24 'answers queries in O(1) time without changing its state', §4.8.3 and p.63 'Queries read the color array'
--   - reading: with high probability: 1 − n^{−c} for suitable constant c (§3) → for every fixed natural exponent, with the program and constants chosen after the exponent; reason: the proofs give every exponent: Lemma 4.24 'for every fixed a > 0', Corollary 6.3 'For every fixed c > 0'; the algorithm depends on the exponent (q copies; L in §5.4); since n ≥ 2, a natural exponent implies every smaller real one
--   - encoding: an adaptive adversary, which chooses each update from the previously completed states but not the fresh randomness → every reachable completed state and every legal next update, with probability over fresh coins; reason: the paper's own form, p.63: 'Both time guarantees hold after fixing the preceding history and the next update'; it implies the bound against every such adversary
--   - reading: maintain a proper ∆-coloring → every reachable completed state serves a proper {1,…,∆}-coloring of its current graph, and every update completes with probability one; reason: Corollary 6.3 'always maintains', 'terminates with probability one'; Lemma 4.24 'remains always correct'
--   - encoding: natural logarithms, log_∆ n → Real.log, log_∆ n = log n / log ∆; reason: with n > ∆ ≥ 16 both logarithms are positive
--   - encoding: words of space → the number of memory cells written so far, at every reachable completed state; reason: a cell counts once written; cells never written are the initial zero memory
--   - encoding: conditional expectation of the update time → the lower Lebesgue integral of the ℕ∞-valued time from the fixed state over fresh coins; reason: an ℕ∞-valued time has a well-defined expectation; a run that never completes has time ∞
--   - encoding: changes the colors of at most O(log_∆ n) vertices between consecutive completed states → the number of vertices whose queried color differs between the state before the update and the completed state after it, on every tape; reason: the stored coloring is what queries read; p.62: 'at most L + 4 vertex colors change', and failed attempts contribute no changes
--   - reading: 'Fix 16 ≤ ∆ < n. There is a randomized fully dynamic algorithm' → one program for all n and ∆ in the range, which receives n and ∆ as input words; reason: the algorithm of the proof takes them as parameters (the length limit L of §5.4 is computed from them); a program depending on n would be nonuniform
--   - reading: polynomial preprocessing → preprocessing takes at most Cn^{c′} steps on every tape, with c′ chosen before c; reason: the initialization is deterministic (Theorem 5.7: static Brooks start, p.63), and its exponent does not depend on c
-- source:
--   Mishra, Mukherjee, Fully Dynamic Brooks Coloring (STOC 2027 submission, preprint, sha256 6542a9f18a48e0b539c2aadee984a641d38a01a551fd32d5fa4d4c5164e32d7b), Theorem 5.7, p.63 (PDF 65)

import Mathlib
import Definitions.Def_DynBrooks_Machine
import Definitions.Def_DynBrooks_Protocol

open MeasureTheory ENNReal

namespace DynBrooks

/-- **Theorem 5.7** (Mishra, Mukherjee, *Fully Dynamic Brooks Coloring*, STOC 2027 submission,
sha256 6542a9f1…, p.63 (PDF 65)). Fix `16 ≤ ∆ < n`. There is a randomized fully dynamic algorithm for
graphs on `[n]` of maximum degree at most `∆`, with no `K_{∆+1}`, that always maintains an explicit proper
`[∆]`-coloring against an adaptive adversary. Each update takes `O(∆ log_∆ n)` time in expectation and
with high probability, and a color query takes `O(1)` time. Both time guarantees hold after fixing the
preceding history and the next update. The algorithm uses `O(n²)` words of space and polynomial
preprocessing, and changes the colors of at most `O(log_∆ n)` vertices between consecutive completed
states.

**Formalization Note.** Machine, protocol, `Reach`, `Serves`, natural logarithms and
`log_∆ n = log n / log ∆` as in `theorem_1_1`. "With high probability" is `1 − n^{−c}` for every fixed
`c > 0`, the program and constants chosen after `c` (the length limit `L` of §5.4 depends on `c`). "After
fixing the preceding history and the next update" is: from every reachable completed state `s` and every
legal next update, under fresh coins; the expectation is the lower Lebesgue integral of the `ℕ∞`-valued
time. Space is the number of memory cells ever written; recolored vertices are those whose queried color
differs between `s` and the completed state reached after the update. Always maintaining a coloring
includes completing each update with probability one. -/
theorem theorem_5_7 :
    ∃ c' : ℕ, ∀ c : ℕ, 0 < c → ∃ C W₀ : ℕ, ∃ P : Program,
      ∀ n Δ : ℕ, 16 ≤ Δ → Δ < n → ∀ w : ℕ, W₀ * (Nat.clog 2 n + 1) ≤ w →
      ∀ G₀ : SimpleGraph (Fin n), IsBrooks Δ G₀ →
      ∀ es : List (Fin n × Fin n), IsEdgeListing G₀ es →
        (∀ ω : ℕ → BitVec w, time P ω (startConfig w Δ es) ≤ ((C * n ^ c' : ℕ) : ℕ∞)) ∧
        ∀ (s : Config w) (G : SimpleGraph (Fin n)), Reach P Δ es G₀ s G →
          Serves P C Δ s G ∧ s.written.card ≤ C * n ^ 2 ∧
          ∀ x : Update n, IsLegal Δ G x →
            ∫⁻ ω, ((time P ω (feed s x.words) : ℕ∞) : ℝ≥0∞) ∂coinMeasure w ≤
              ENNReal.ofReal ((C : ℝ) * Δ * (Real.log n / Real.log Δ)) ∧
            coinMeasure w {ω | ENNReal.ofReal ((C : ℝ) * Δ * (Real.log n / Real.log Δ)) <
                ((time P ω (feed s x.words) : ℕ∞) : ℝ≥0∞)} ≤
              ENNReal.ofReal ((n : ℝ) ^ (-(c : ℝ))) ∧
            coinMeasure w {ω | time P ω (feed s x.words) = ⊤} = 0 ∧
            ∀ (ω : ℕ → BitVec w) (s' : Config w), complete P ω (feed s x.words) = some s' →
              (recolored n P s s' : ℝ) ≤ C * (Real.log n / Real.log Δ) := by sorry

end DynBrooks
