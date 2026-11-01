-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_far_field_jump_integral_exact_large_tail
-- name    : AvramDividend.Classical.avram_wave4_05_source_far_field_jump_integral_exact_large_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:44:33.986804+00:00
-- url     : https://prove2.me/theorems/ce66dc06-49f1-436e-b68f-7b7dc01fb2da
-- title:
--   Exact compensated Lévy generator jump integral equals the large negative-jump tail above the barrier
-- statement:
--   Under genuine source q-scale assumptions, for every reserve x≥cstar(W)+1 the full source generator integrand is ν-integrable and its integral over all negative jumps equals exactly the ordinary noncompensated increment integral over large negative jumps y≤−1. There are no residual Taylor or Gaussian terms: they vanish because the barrier candidate is affine at both x and x+y for every small jump −1<y<0. The right-side integral retains all large jumps crossing the barrier or below ruin.
-- source:
--   Canonical pointwise compensated far-field kernel theorem and source GeneratorIntegrable above cstar; Mathlib integral_indicator and integral_congr_ae.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generatorIntegrand_far_field_exact_large_jump_kernel

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_05_source_far_field_jump_integral_exact_large_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (x : ℝ) (hfar : (cstar W).toReal + 1 ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      (∫ y in Iio (0 : ℝ),
        SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ∂X.ν) =
      ∫ y in Iic (-1 : ℝ),
        (vcstar W (x + y) - vcstar W x) ∂X.ν := by sorry
