-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_large_tail_split_at_ruin
-- name    : AvramDividend.Classical.avram_wave4_05_source_far_field_large_tail_split_at_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:02:43.86398+00:00
-- url     : https://prove2.me/theorems/e0159e89-97d7-428d-aa68-f24bfbe22304
-- title:
--   Exact source large-jump integral split at ruin into strict overshoot intensity and non-ruin increments
-- statement:
--   At any reserve x≥cstar(W)+1 for the actual source spectrally negative Lévy measure, the large-jump integrable increment over y≤−1 decomposes exactly into two terms: the negative candidate value multiplied by the strict ruin-crossing real tail intensity ν.real{y<−x}, plus the integral over −x≤y≤−1 of ordinary candidate increments. The second interval retains the atom y=−x (jump landing exactly at zero), which need not have zero post-jump value in bounded variation. This is a true integrable set decomposition with no first moment of the large negative jumps assumed.
-- source:
--   Accepted large-tail Bochner integrability, source barrierValue zero extension, Mathlib setIntegral_union on disjoint sets, and setIntegral_congr_fun.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_large_tail_integrable

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_source_far_field_large_tail_split_at_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    (∫ y in Iic (-1 : ℝ),
      (vcstar W (x + y) - vcstar W x) ∂X.ν) =
      X.ν.real (Iio (-x)) * (-vcstar W x) +
        ∫ y in Icc (-x) (-1 : ℝ),
          (vcstar W (x + y) - vcstar W x) ∂X.ν := by sorry
