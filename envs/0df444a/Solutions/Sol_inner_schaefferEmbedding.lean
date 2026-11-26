-- Prove2me | solution 1 for inner_schaefferEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:18:09.89702+00:00
-- url     : https://prove2.me/submissions/cfee9891-6397-4aa8-9c41-0ac148b4ec5c

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
omit [CompleteSpace E]
theorem _root_.solution (x y : E) :
    ⟪schaefferEmbedding x, schaefferEmbedding y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [schaefferEmbedding_apply, lp.inner_single_left, lp.single_apply_self]
