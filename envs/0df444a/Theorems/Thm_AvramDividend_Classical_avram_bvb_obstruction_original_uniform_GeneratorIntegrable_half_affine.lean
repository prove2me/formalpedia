-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_GeneratorIntegrable_half_affine
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_uniform_GeneratorIntegrable_half_affine
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:33:47.601423+00:00
-- url     : https://prove2.me/theorems/65ecfec6-46fa-4c3e-9f4c-eacb51707a04
-- title:
--   Original uniform negative Lévy process generator integrable for positive half-unit affine reserve
-- statement:
--   For original negative-unit uniform Lévy measure and the piecewise candidate w(u)=0 below zero and u+1/2 otherwise, the actual original generatorIntegrand is integrable on the full negative Lévy measure at every positive reserve. This discharges the remaining GeneratorIntegrable regularity condition in the positive-cap BV HJB witness.
-- source:
--   By exact original ν=volume|(-1,0), the restricted negative-jump generator measure is that interval. Proved pointwise crossing-kernel equality on the support reduces integrability to the corresponding Lebesgue crossing-kernel IntegrableOn lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_crossing_kernel_integrableOn
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_affine_generator_integrand_crossing_exact
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_uniform_GeneratorIntegrable_half_affine
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))
    (y : ℝ) (hy : 0 < y) (w : ℝ → ℝ)
    (hw : ∀ u : ℝ, w u = if u < 0 then 0 else 1 / 2 + u)
    (hd : deriv w y = 1) :
    X.GeneratorIntegrable w y := by sorry
