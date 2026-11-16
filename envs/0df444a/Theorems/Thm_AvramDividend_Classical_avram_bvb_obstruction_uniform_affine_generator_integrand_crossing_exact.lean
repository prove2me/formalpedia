-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_uniform_affine_generator_integrand_crossing_exact
-- name    : AvramDividend.Classical.avram_bvb_obstruction_uniform_affine_generator_integrand_crossing_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T01:05:30.929458+00:00
-- url     : https://prove2.me/theorems/63a9f24e-2520-427d-8ab0-a76807a1ed07
-- title:
--   Original compensated generator integrand for positive affine reserve and negative unit jump equals crossing kernel
-- statement:
--   On positive reserve y and a negative unit Lévy mark z, for the candidate w(u)=0 when u<0 and 1/2+u otherwise, and derivative w′(y)=1, the original compensated Lévy SpectrallyNegativeLevy.generatorIntegrand equals −(y+1/2+z) if the mark crosses zero and vanishes otherwise. This identifies exactly the source mark-integrand used by the uniform compound Poisson HJB witness.
-- source:
--   Use the original SpectrallyNegativeLevy.generatorIntegrand definition and truncation indicator on (-1,1), where negative unit marks all lie. Substitute w(y)=y+1/2 and the piecewise w(y+z) and simplify both crossing cases. Does not replace source reserve or jump convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_bvb_obstruction_uniform_affine_generator_integrand_crossing_exact
    (y z : ℝ) (hy : 0 < y) (hz : z ∈ Ioo (-1 : ℝ) 0)
    (w : ℝ → ℝ)
    (hw : ∀ u : ℝ, w u = if u < 0 then 0 else 1 / 2 + u)
    (hd : deriv w y = 1) :
    SpectrallyNegativeLevy.generatorIntegrand w y z =
      if y + z < 0 then -(y + (1 / 2 : ℝ) + z) else 0 := by sorry
