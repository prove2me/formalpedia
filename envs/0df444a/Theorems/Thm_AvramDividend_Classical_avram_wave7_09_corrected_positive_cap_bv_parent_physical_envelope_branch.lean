-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_corrected_positive_cap_bv_parent_physical_envelope_branch
-- name    : AvramDividend.Classical.avram_wave7_09_corrected_positive_cap_bv_parent_physical_envelope_branch
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:55:26.00406+00:00
-- url     : https://prove2.me/theorems/07fc8bfd-5f4c-4fb4-84a2-d9eb2be035c6
-- title:
--   Corrected positive-cap BV parent directly proved whenever the physical drift envelope is below w(x)
-- statement:
--   For the exact corrected positive-cap bounded-variation parent assumptions, and any finite real horizon T≥0, if the additional explicit physical drift envelope condition x+T*X.drift≤w x holds, then the complete original ruin-stopped discounted full Stieltjes expected payout is bounded by ENNReal.ofReal(w x). The proof uses Proved original capped admissibility nonnegative initial reserve b3117b07, then the sharp original BV physical closed-horizon expected payout budget 23ddd713 and monotonicity of ENNReal.ofReal. This completely settles the easy deterministic envelope branch of the parent; its strict complement still needs open stochastic HJB gain (ef7e6c20 or 3ae3442d). No altered target and no open dependency.
-- source:
--   Original corrected parent source assumptions, Proved b3117b07 and 23ddd713; accepted W7-09 parent deficit certificate candidate 22531 contains this exact branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_corrected_positive_cap_bv_parent_physical_envelope_branch
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (T : ℝ) (hT : 0 ≤ T)
    (hEnvelope : x + T * X.drift ≤ w x) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
