-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_vcstar_contact_lipschitz_from_positive_band_deriv
-- name    : AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_contact_lipschitz_from_positive_band_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:43:09.423389+00:00
-- url     : https://prove2.me/theorems/ea510ffd-5b8f-41d6-a09a-a4fe3eca4513
-- title:
--   Original BV barrier value has a contact Lipschitz and derivative envelope on every controlled positive band
-- statement:
--   For the actual BV barrier value, original regularity plus a finite derivative bound on a positive band controls every contact increment remaining in that band by the derivative envelope. This supplies both hypotheses in the already-Proved contact Taylor inequality, without any claim about a ruin-crossing cell.
-- source:
--   Specialise the Proved original vcstar BV C1 regularity on (0,∞) to the compact interior band, obtain differentiability at its points, then apply the exact pinned Mathlib convex mean-value estimate norm_image_sub_le_of_norm_deriv_le. The second bound is the given local derivative envelope; no BV prebudget is involved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_unrestricted_verification_regularity
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_ruin8_vcstar_contact_lipschitz_from_positive_band_deriv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation) (a b L : ℝ) (ha : 0 < a) (hL : 0 ≤ L)
    (hBound : ∀ z ∈ Set.Icc a b, |deriv (vcstar W) z| ≤ L)
    (z c : ℝ) (hz : z ∈ Set.Icc a b) (hzc : z + c ∈ Set.Icc a b) :
    |vcstar W (z + c) - vcstar W z| ≤ L * |c| ∧
    |deriv (vcstar W) z| ≤ L := by sorry
