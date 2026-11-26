-- Prove2me | solution 1 for schaefferBilateralShift_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:17.819549+00:00
-- url     : https://prove2.me/submissions/516c8a3d-37c5-44b1-bd96-55aa38d499bf

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Algebra.Star.Unitary
import Definitions.Def_Operator_Dilation_Halmos
import Definitions.Def_Operator_Dilation_Schaeffer

set_option autoImplicit false
open scoped ENNReal InnerProductSpace
universe u
noncomputable section
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution :
    schaefferBilateralShift (E := E) ∈
      unitary (SchaefferSpace E →L[ℂ] SchaefferSpace E) :=
  (schaefferBilateralShiftUnitary (E := E)).property
