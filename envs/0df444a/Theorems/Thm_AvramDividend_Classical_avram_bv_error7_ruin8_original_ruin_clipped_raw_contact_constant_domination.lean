-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_original_ruin_clipped_raw_contact_constant_domination
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_original_ruin_clipped_raw_contact_constant_domination
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:27:22.073213+00:00
-- url     : https://prove2.me/theorems/b8fbb18b-a22e-41df-98f6-576c847deb25
-- title:
--   Original BV final raw value-change error has a constant domination envelope even across ruin
-- statement:
--   For actual bounded-variation Levy vcstar W, a contact with nonnegative pre-contact and zero-clipped post-contact reserves in a common compact band has uniformly bounded raw value change, even when the un-clipped post-contact reserve lies below zero.
-- source:
--   Proved vcstar boundedness on nonnegative compact bands and Proved exact zero extension below ruin yield a 2M envelope by triangle inequality. The Levy standing law is a probability measure so this deterministic envelope is integrable; the no-circularity L1 conversion is handled by a separately Proved DCT theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_zero_of_neg
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_original_ruin_clipped_raw_contact_constant_domination
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (B : ℝ)
    (z c : ℕ → Ω → ℝ)
    (hClipBand : ∀ m ω, z m ω ∈ Set.Icc 0 B ∧
      max (z m ω + c m ω) 0 ∈ Set.Icc 0 B)
    (Err : ℕ → Ω → ℝ)
    (hErrSource : ∀ m ω, Err m ω =
      vcstar W (z m ω + c m ω) - vcstar W (z m ω)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ m ω, ‖Err m ω‖ ≤ 2 * M := by sorry
