-- Prove2me | solution 1 for numericalRange_eq_empty_iff_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:41.539081+00:00
-- url     : https://prove2.me/submissions/941feddd-2276-48cb-997a-d03bfac8488e

import Mathlib.Analysis.Normed.Module.Normalize
import Definitions.Def_Operator_NumericalRange_Basic
import Definitions.Def_Operator_NumericalRange_Nonempty
import Theorems.Thm_numericalRange_nonempty_iff_nontrivial

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) :
    numericalRange A = ∅ ↔ Subsingleton E := by
  rw [← Set.not_nonempty_iff_eq_empty, numericalRange_nonempty_iff_nontrivial,
    not_nontrivial_iff_subsingleton]
