-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_compensated_jump_integral_nonpos
-- name    : AvramDividend.Classical.avram_wave4_05_source_far_field_compensated_jump_integral_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:39:35.804968+00:00
-- url     : https://prove2.me/theorems/7fc26730-9a73-4276-9c41-2360e28eadf4
-- title:
--   Full original-source compensated jump integral is nonpositive one unit above the optimal barrier
-- statement:
--   For a spectrally negative Lévy process under standing assumptions, a positive discount rate, and the canonical q-scale function W, at any reserve x≥cstar+1 the genuine source generator jump integrand is integrable over all negative jump sizes and its whole ν-integral is nonpositive. The proof splits −1<y<0, where affine barrier continuation makes the exact compensated integrand zero, from y≤−1, where the full uncompensated large jump, even crossing below ruin, has nonpositive increment by global monotonicity.
-- source:
--   Genuine SpectrallyNegativeLevy.generatorIntegrand and GeneratorIntegrable; Proved cstar finite, vcstar monotone, small-jump exact cancellation, and positive-reserve generator domain.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_finite_cstar
import Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_05_source_far_field_compensated_jump_integral_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ)
    (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) ≤ 0 := by sorry
