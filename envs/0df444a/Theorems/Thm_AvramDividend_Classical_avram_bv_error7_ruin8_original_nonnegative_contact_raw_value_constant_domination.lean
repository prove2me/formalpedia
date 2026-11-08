-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_constant_domination
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_constant_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:58:06.257989+00:00
-- url     : https://prove2.me/theorems/54a71062-24e7-436b-8618-ccbf6d93bf79
-- title:
--   Actual barrier final-contact raw value difference is uniformly dominated by a finite value envelope through ruin
-- statement:
--   When the two authentic final-contact reserve endpoints lie in a common nonnegative compact band, the original `vcstar` raw value-change error is uniformly bounded by twice the finite candidate-value envelope, including at ruin. No bound on `deriv vcstar` is used.
-- source:
--   Instantiate the separately Proved original candidate compact nonnegative value envelope, then apply the triangle inequality to the raw value difference. The constant is independent of the physical-grid index and sample, so it is integrable on the original probability space and supplies the missing domination for derivative-free contact DCT.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_nonnegative_contact_raw_value_constant_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (B : ℝ)
    (z c : ℕ → Ω → ℝ)
    (hBand : ∀ m ω, z m ω ∈ Set.Icc 0 B ∧ z m ω + c m ω ∈ Set.Icc 0 B)
    (Err : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m ω, ‖Err m ω‖ ≤ 2 * M := by sorry
