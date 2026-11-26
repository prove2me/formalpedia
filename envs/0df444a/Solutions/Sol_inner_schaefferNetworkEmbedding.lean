-- Prove2me | solution 1 for inner_schaefferNetworkEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:37:49.299872+00:00
-- url     : https://prove2.me/submissions/5d6c2476-236a-44ee-8060-7cac737507eb

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
    ⟪schaefferNetworkEmbedding x, schaefferNetworkEmbedding y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [schaefferNetworkEmbedding_apply, lp.inner_single_left,
    lp.single_apply_self, WithLp.prod_inner_apply, inner_zero_right, add_zero]
