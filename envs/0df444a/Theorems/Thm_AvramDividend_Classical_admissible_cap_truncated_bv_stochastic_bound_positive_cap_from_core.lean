-- Prove2me | Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_bv_stochastic_bound_positive_cap_from_core
-- name    : AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_bound_positive_cap_from_core
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T07:23:23.11489+00:00
-- url     : https://prove2.me/theorems/8c16239e-24e6-4d16-949d-5a1784439875
-- title:
--   Corrected positive-cap BV stopped verification bound reduced to the source-specific stochastic core
-- statement:
--   For an original spectrally negative Levy process under the BV standing hypotheses, a positive reserve cap, nonnegative candidate boundary value w(0), and initial capital within that cap, a C1 HJB supersolution dominates the complete discounted pre-ruin Stieltjes dividends at every finite horizon. All other assumptions and the conclusion are the legacy canonical BV stochastic parent. The missing initial nonnegative capital and original-source right-dividend jump-drop conditions follow from two existing Proved theorems, so the only unproved analytical input is the positive-cap BV stochastic core. This separate new theorem does not amend the defective legacy parent and is not itself a parent-child graph edge.
-- source:
--   Corrected source-specific replacement bridge for legacy BV parent 65617e0a-5e27-4272-bb37-8905da7da981, whose zero-cap case is refuted by Proved theorem c4bc3559-e543-4e60-a052-fd6eca321c1a. The new statement adds hC, hw0, hxc and preserves exact Stieltjes cash and t=0 atom. Derive hx from Proved b3117b07-8383-4143-a965-2d9876a04a99 and hjump from Proved 2cd50555-c982-414f-b6aa-527b1d3ba42a; the remaining dependency is Open positive-cap core ef7e6c20-a118-46f0-ac94-5b02204bba49.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.admissible_cap_truncated_bv_stochastic_bound_positive_cap_from_core
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
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
