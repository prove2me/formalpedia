-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_convex_smalljump_generator_integrand_nonnegative
-- name    : AvramDividend.Classical.avram_f6_original_convex_smalljump_generator_integrand_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T22:34:54.846751+00:00
-- url     : https://prove2.me/theorems/5a0df0a5-24f6-4b59-81bd-feed1e98edcb
-- title:
--   Convex original HJB candidate gives nonnegative exact compensated Lévy small negative jump integrand
-- statement:
--   For global convex differentiable real w, any original small negative mark -1<z<0 has actual generatorIntegrand w y z≥0, using the true original compensated Lévy generator integrand identity and exact Mathlib convex supporting tangent inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_convex_smalljump_generator_integrand_nonnegative
    (w : ℝ → ℝ) (hConvex : ConvexOn ℝ Set.univ w)
    (y z : ℝ) (hDiff : DifferentiableAt ℝ w y)
    (hz1 : -1 < z) (hz0 : z < 0) :
    0 ≤ SpectrallyNegativeLevy.generatorIntegrand w y z := by sorry
