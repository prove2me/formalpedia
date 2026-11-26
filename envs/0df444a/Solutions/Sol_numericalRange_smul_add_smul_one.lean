-- Prove2me | solution 1 for numericalRange_smul_add_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:14:00.186485+00:00
-- url     : https://prove2.me/submissions/f0591e1b-5fd0-46de-aa14-d9a5ec450400

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_AffineClosure
import Theorems.Thm_numericalRange_add_smul_one
import Theorems.Thm_numericalRange_smul


set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (a b : ℂ) :
    numericalRange (a • A + b • 1) =
      (fun z => a * z + b) '' numericalRange A := by
  rw [numericalRange_add_smul_one, numericalRange_smul, Set.image_image]
