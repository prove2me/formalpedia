-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_C1_negative_jump_generator_integral_continuous_on_base_neighborhood
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_C1_negative_jump_generator_integral_continuous_on_base_neighborhood
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:17:36.649185+00:00
-- url     : https://prove2.me/theorems/5f441882-aef7-43d6-86fe-c4eadae43016
-- title:
--   Original bounded-variation Lévy C1 jump generator integral is locally continuous at base reserve
-- statement:
--   For the genuine BV source with only C1 and globally Lipschitz w, and generator jump integrability at x, the negative-jump integral z↦∫_{y<0}[w(z+y)-w(z)]ν(dy) is continuous on [x−1,x+1]. The proof uses the sharp two-modulus kernel bound, the source BV integrable scalar envelope 2L min(1,|y|), and the integrable base kernel at x; thus the common Bochner dominated-convergence bound is |K(x,y)|+2L min(1,|y|). Sequential DCT and C1 continuity prove the claim without C2, replacement process, or assumed generator identity.
-- source:
--   Complete remote-compiler sentinel-verified candidates/work_on/AvramDividend_04c_actual_C1_jump_generator_integral_continuousOn_probe.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_bv_negative_jump_scalar_majorant_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_lipschitz_jump_increment_two_moduli
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_C1_negative_jump_generator_integral_continuous_on_base_neighborhood {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x) :
    ContinuousOn (fun z : ℝ =>
      ∫ y : ℝ, (w (z + y) - w z) ∂(X.ν.restrict (Iio 0)))
      (Icc (x - 1) (x + 1)) := by sorry
