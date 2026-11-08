-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:49:21.703089+00:00
-- url     : https://prove2.me/theorems/c886a118-f477-473e-91e7-f77037e2a393
-- title:
--   Original BV barrier contact value has a uniform finite bound through zero on compact nonnegative reserves
-- statement:
--   The actual BV barrier candidate has a finite absolute bound on every nonnegative compact reserve band including zero. This is the domination constant for a derivative-free contact raw value-change limit and avoids an unproved derivative bound near ruin.
-- source:
--   Use the Proved source-specific global continuity on Ici 0, restrict to Icc 0 B, and take the compact image of its absolute value. Its bounded-above property supplies a nonnegative uniform magnitude bound, with no BV signed budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_bounded_value_on_nonnegative_contact_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hbv : X.BoundedVariation) (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Set.Icc 0 B, |vcstar W z| ≤ M := by sorry
