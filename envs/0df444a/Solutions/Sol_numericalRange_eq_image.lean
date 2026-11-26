-- Prove2me | solution 1 for numericalRange_eq_image
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:27:00.076668+00:00
-- url     : https://prove2.me/submissions/38edda8e-2b17-4a9c-a0a9-19dc642c015c

import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Compact
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    numericalRange A = (fun x => ⟪x, A x⟫_ℂ) '' Metric.sphere (0 : E) 1 := by
  ext z
  simp only [mem_numericalRange, Set.mem_image, mem_sphere_zero_iff_norm]
