-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_BV_HJB_stopping_criteria
-- name    : AvramDividend.Classical.avram_sweep18_original_BV_HJB_stopping_criteria
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:07:12.050053+00:00
-- url     : https://prove2.me/theorems/88794ba3-ff17-47cb-a447-17a40f512fce
-- title:
--   Original bounded-variation HJB components, reserve nonnegativity and time-zero-inclusive jump secant
-- statement:
--   For the identical original spectrally negative Levy process and capped admissible strategy, original BV smoothness and HJB max equality imply the generator upper inequality, slope lower bound, nonnegative pre-ruin candidate on the actual reserve and the canonical time-zero-or-strict-pre-ruin right-payment jump secant. Exact HJB decomposition, capped reserve range and original C1 secant are already Proved. This packages the nonstochastic inputs to the original BV signed stopping budget and finite-horizon verifier without changing assumptions or horizon atoms.
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

theorem AvramDividend.Classical.avram_sweep18_original_BV_HJB_stopping_criteria
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
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
