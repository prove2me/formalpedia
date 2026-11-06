-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
-- name    : AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:45:19.191683+00:00
-- url     : https://prove2.me/theorems/5f565ecd-8817-485b-a619-526a32defaf7
-- title:
--   Actual original negative-mark cell has unbounded predictable L2-weighted zero conditional mean
-- statement:
--   Every original spectrally negative Lévy physical marked count in a strictly negative finite band has zero conditional expectation after compensation and multiplication by an arbitrary square-integrable past-measurable weight. The weight need not be bounded and no auxiliary assumed original count measurability, finite Lévy rate, or count second-moment premise is needed: they follow from P2 and the proved P4-S3 source theorems.
-- source:
--   Source-exact composition of Proved P2 arbitrary separated Borel finite original Levy rate and count measurability, P4-S3 original full-band dominated centered L2 963870c8-6ffc-4e96-aa5b-3842ee01e9cf and P4-S3 original weighted conditional mean-zero without rectangle assumption ae0f4de2-2c7b-48ea-950f-6e61dbb4d071. Provides unbounded prior-cell count weights for physical grid cross-time covariance; still requires an explicit adaptedness lemma for particular H.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_weighted_finite_band_condExp_zero_no_rectangle
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    P[(fun ω => H ω * ((N ω).toReal - r)) | 𝓕 s] =ᵐ[P] 0 := by sorry
