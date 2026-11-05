-- Prove2me | Theorems.Thm_CorrelatedRounding_lemma_1
-- name    : CorrelatedRounding.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:46.970582+00:00
-- url     : https://prove2.me/theorems/c97b9ddc-9887-4c39-9566-2da4c18672ff
-- title:
--   Lemma 1 — Algorithm 1 has the exact marginals
-- statement:
--   Let $(E_k)_k$ be a draw of Algorithm 1 on a probability space, and let $Z$ take values almost surely in the arg min of the clocks. Then, for every item $i$ and every FC $k$,
--   $$\Pr[Z_i=k]=u_{ki}.$$
--   This is the marginals condition that makes Algorithm 1 a rounding scheme.
--
--   **Formalization Note.** $Z$ carries no measurability hypothesis, and the measure of a possibly non-measurable set is outer measure.
--
--   Differences from the source:
--   - reading: "Break ties arbitrarily" → every Z valued almost surely in the arg min, with no measurability and no fixed rule; μ of a possibly non-measurable set is outer measure; reason: the strongest reading; it covers every tie rule, because ties between finite clocks are null events
--   - generalization: "Assume without loss that y_k > 0 for all k" (p.9) → an FC with y_k = 0 is allowed, and its entry of the draw is unconstrained; reason: such an FC has clock ∞ at every item; the page's instances, all y_k > 0, are a special case
--   - encoding: items i = 1,…,q and FCs k = 1,…,K → Fin q and Fin K, both 0-based; reason: Lean convention; same instances
--   - encoding: (y_k/u_ki) E_k = ∞ if u_ki = 0 (p.9) → the clock is ⊤ : EReal at u_ki = 0; reason: the page's convention; only ≤ is applied to clocks
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, Lemma 1, p.10

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw

open MeasureTheory ProbabilityTheory

namespace CorrelatedRounding

/-- **Lemma 1.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4, p.10:
"Under Algorithm 1, Pr[Z_i = k] = u_ki for all i = 1,…,q and k = 1,…,K."

**Formalization Note.** `Z` is any function valued almost surely in the arg min, with no measurability and
no fixed rule ("break ties arbitrarily"). `μ` of a possibly non-measurable set is outer measure. The clause
stays true because ties between finite clocks are null events. FCs with `u_ki = 0` are included: the value
is `0`. -/
theorem lemma_1 {q K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {u : Fin K → Fin q → ℝ} (hu : IsInstance u) {E : Fin K → Ω → ℝ}
    (hE : IsAlg1Draw u μ E) {Z : Ω → Fin q → Fin K}
    (hZ : ∀ᵐ ω ∂μ, IsAlg1Output u (fun k => E k ω) (Z ω)) (i : Fin q) (k : Fin K) :
    μ {ω | Z ω i = k} = ENNReal.ofReal (u k i) := by sorry

end CorrelatedRounding
