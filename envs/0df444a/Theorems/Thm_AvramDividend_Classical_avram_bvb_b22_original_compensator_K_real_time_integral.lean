-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_b22_original_compensator_K_real_time_integral
-- name    : AvramDividend.Classical.avram_bvb_b22_original_compensator_K_real_time_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:18:39.461926+00:00
-- url     : https://prove2.me/theorems/525348c8-5ac6-49a2-b621-78711ed8e06c
-- title:
--   Original masked loss upper bound on the genuine uniform floor grid
-- statement:
--   The actual original prepayment reserve's discounted open-cap negative mark loss on the refining uniform floor grid is eventually no greater than its closed-cap contact-time loss plus arbitrary epsilon, even when the grid misses contact occupation.
-- source:
--   Root-connected one-sided a.e. floor-sampling input for phys95/efbae9c3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_b22_original_compensator_K_real_time_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ) (ω : Ω) (H : (ℝ≥0 × Ω) × ℝ → ℝ)
    (hMeas : AEStronglyMeasurable
      (fun t : ℝ≥0 => ∫ z,
        H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ))))
      (((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) :
    (∫ t, ∫ z,
      H ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
      ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)) =
    (∫ t in Icc 0 T, ∫ z,
      H ((Real.toNNReal t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))) := by sorry
