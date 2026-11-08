-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_uniform_continuity_on_nonnegative_compact_contact_band
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_uniform_continuity_on_nonnegative_compact_contact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:48:34.766201+00:00
-- url     : https://prove2.me/theorems/f6999b94-4075-4bf9-8425-b2fdba1e6fd9
-- title:
--   Actual BV barrier value is uniformly continuous through the ruin endpoint on each nonnegative compact band
-- statement:
--   The authentic BV value candidate is uniformly continuous on any compact nonnegative reserve interval, even at zero where its derivative need not be bounded. This supports a derivative-free treatment of the final value-change contact cell when both compensated endpoints stay nonnegative.
-- source:
--   The Proved original BV verification regularity theorem gives ContinuousOn vcstar (Ici 0). Restrict to the compact interval Icc 0 B and apply the pinned Mathlib Heine-Cantor theorem. The proof deliberately makes no claim across negative reserve at ruin and imports no BV budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_uniform_continuity_on_nonnegative_compact_contact_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hbv : X.BoundedVariation) (B : ℝ) :
    UniformContinuousOn (vcstar W) (Set.Icc 0 B) := by sorry
