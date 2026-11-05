-- Prove2me | Theorems.Thm_CorrelatedRounding_display_p12
-- name    : CorrelatedRounding.display_p12
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:12.371025+00:00
-- url     : https://prove2.me/theorems/b00f6c93-ea1f-4f70-b255-b54b04a2ef9e
-- title:
--   Proof of Theorem 1, p.12 — the union bound on arrivals
-- statement:
--   Fix an FC $k$ with $y_k>0$, a draw of Algorithm 1, and gaps $G_j$ of rate $y_k$ independent of each other and of the draw. Set $S^1=E_k$ and $S^{j+1}=S^j+G_j$. Then
--   $$\Pr\Big[\bigcup_{i:u_{ki}>0}\bigcup_{j\ge1}\Big(\min\Big\{\min_{k'\ne k}\frac{y_{k'}}{u_{k'i}}E_{k'},\ \min_{j'<j}\frac{y_k}{u_{ki}}S^{j'}\Big\}\ge\frac{y_k}{u_{ki}}S^j\Big)\Big]\le y_k\int_0^\infty\min\{q e^{-t},1\}\,dt .$$
--   This combines display (1) with Lemma 2. It decouples the opening of FC $k$ from the event that some item is still waiting.
--
--   Differences from the source:
--   - reading: a chain of five lines whose three middle lines condition on "∃j : S^j_k = t" → the first line ≤ the last line; reason: the conditioning is Palm conditioning for a Poisson process, not elementary conditioning; the middle lines are the proof and the end points are the claim
--   - encoding: the S^j_k as arrival times of a Poisson process of rate y_k → S 0 = E k, S (j+1) = S j + G j, with the G j of law Exp(rate y_k) and Sum.elim E G independent; reason: the page's own "more specifically" construction, p.11
--   - generalization: "Assume without loss that y_k > 0 for all k" (p.9) → only the fixed FC needs y_k > 0; another FC may have y_k = 0, with an unconstrained draw entry; reason: such an FC has clock ∞ at every item; the page's instances are a special case
--   - encoding: items i = 1,…,q and FCs k = 1,…,K → Fin q and Fin K, both 0-based; reason: Lean convention; same instances
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, proof of Theorem 1, display, p.12

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw

open MeasureTheory ProbabilityTheory

namespace CorrelatedRounding

/-- **The union bound display.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4, proof of Theorem 1, p.12, first line ≤ last line:
"Pr[⋃_{i:u_ki>0} ⋃_{j=1}^∞ (min{min_{k′≠k} (y_{k′}/u_{k′i}) E_{k′}, min_{j′<j} (y_k/u_ki) S^{j′}_k} ≥ (y_k/u_ki) S^j_k)]
≤ y_k ∫_0^∞ min{q e^{−t}, 1} dt".

Here `S 0 = E k` and `S (j+1) = S j + G j`, with gaps `G j` of law `Exp(rate y_k)` independent of each other and
of the draws (p.11: "S^{j+1}_k be the sum of S^j_k with an independent Exponential random variable of mean
1/y_k").

**Formalization Note.** The three middle lines of the display condition on "∃ j : S^j_k = t", which is Palm
conditioning for a Poisson process and not elementary conditioning. They are the proof; the end points are the
claim. Lean's `j = 0` is the page's `j = 1`. The fixed FC has `y_k > 0`, which the paper's standing assumption
gives and the mean `1/y_k` of the gaps needs. -/
theorem display_p12 {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) (k : Fin K) (hk : 0 < y u k) (G : ℕ → Ω → ℝ)
    (hG : ∀ j, HasLaw (G j) (expMeasure (y u k)) μ) (hind : iIndepFun (Sum.elim E G) μ)
    (S : ℕ → Ω → ℝ) (hS0 : ∀ ω, S 0 ω = E k ω) (hS : ∀ j ω, S (j + 1) ω = S j ω + G j ω) :
    μ (⋃ i ∈ {i | 0 < u k i}, ⋃ j, {ω |
        (∀ k', k' ≠ k →
          ((y u k / u k i * S j ω : ℝ) : EReal) ≤ clock u (fun k'' => E k'' ω) k' i) ∧
        ∀ j' < j, y u k / u k i * S j ω ≤ y u k / u k i * S j' ω}) ≤
      ENNReal.ofReal (y u k * ∫ t in Set.Ioi (0 : ℝ), min ((q : ℝ) * Real.exp (-t)) 1) := by sorry

end CorrelatedRounding
