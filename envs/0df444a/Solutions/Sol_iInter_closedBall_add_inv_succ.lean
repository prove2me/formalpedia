-- Prove2me | solution 1 for iInter_closedBall_add_inv_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:09.778276+00:00
-- url     : https://prove2.me/submissions/3f2d6de1-0917-4e5f-9e32-cbadf476b6f0

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_mem_numericalRange
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
omit [CompleteSpace E]
theorem _root_.solution (c : ℂ) (r : ℝ) :
    (⋂ n : ℕ, Metric.closedBall c (r + 1 / ((n : ℝ) + 1))) = Metric.closedBall c r := by
  ext z
  simp only [Set.mem_iInter, Metric.mem_closedBall]
  constructor
  · intro h
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    exact (h n).trans_lt (by linarith)
  · intro h n
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
