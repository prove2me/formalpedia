-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_UBV_HJB_stopping_criteria
-- name    : AvramDividend.Classical.avram_sweep18_original_UBV_HJB_stopping_criteria
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:08:46.8297+00:00
-- url     : https://prove2.me/theorems/1efa471d-334e-488d-8db6-5bd7859c70e5
-- title:
--   Original unbounded-variation HJB components, reserve nonnegativity and time-zero-inclusive C2 jump secant
-- statement:
--   For original unbounded-variation X, C2 regularity and the capped HJB max equality imply generator/slope, nonnegative pre-ruin candidate on the original process and the chronological right-payment jump bound including t=0. The C2-to-C1 restriction is explicit and all original capped admissibility hypotheses are unchanged. This packages the four source prerequisites of the original unbounded-variation stopped Ito verification.
-- source:
--   Pinned Proved local_verification_hjb_implies_components, capped_riskProcess_range_before_ruin_including_zero, hjb_candidate_ge_capital, avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_hjb_implies_components
import Theorems.Thm_AvramDividend_Classical_capped_riskProcess_range_before_ruin_including_zero
import Theorems.Thm_AvramDividend_Classical_hjb_candidate_ge_capital
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_zero_or_strict_preruin_C1_canonical_hjump_without_standing
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_sweep18_original_UBV_HJB_stopping_criteria
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
    (∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) := by sorry
