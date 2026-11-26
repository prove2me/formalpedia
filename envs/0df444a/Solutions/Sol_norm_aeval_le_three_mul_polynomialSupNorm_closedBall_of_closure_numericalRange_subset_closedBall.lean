-- Prove2me | solution 1 for norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:47.26201+00:00
-- url     : https://prove2.me/submissions/c94f729c-f74b-43bd-a4e6-d18b743e3e2a

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Definitions.Def_Operator_Crouzeix_AffineAuxiliary
import Definitions.Def_Operator_Crouzeix_ApproximationSupNorm
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Theorems.Thm_norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_ball
import Theorems.Thm_iInter_closedBall_add_inv_succ
import Theorems.Thm_tendsto_polynomialSupNorm_atTop_of_antitone_isCompact


set_option autoImplicit false
open Complex Polynomial spectrum Filter Topology
open scoped InnerProductSpace Pointwise
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {c : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hW : closure (numericalRange A) ⊆ Metric.closedBall c r) (p : ℂ[X]) :
    ‖aeval A p‖ ≤ 3 * polynomialSupNorm p (Metric.closedBall c r) := by
  let K : ℕ → Set ℂ := fun n => Metric.closedBall c (r + 1 / ((n : ℝ) + 1))
  have hanti : Antitone K := by
    intro m n hmn
    apply Metric.closedBall_subset_closedBall
    have h1 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
    have h2 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have := one_div_le_one_div_of_le h2 h1
    linarith
  have hcompact : ∀ n, IsCompact (K n) := fun n => isCompact_closedBall _ _
  have hnonempty : ∀ n, (K n).Nonempty := fun n =>
    ⟨c, Metric.mem_closedBall_self (by positivity)⟩
  have hlim := tendsto_polynomialSupNorm_atTop_of_antitone_isCompact p K hanti hcompact hnonempty
  rw [show (⋂ n, K n) = Metric.closedBall c r from iInter_closedBall_add_inv_succ c r] at hlim
  have hbound : ∀ n, ‖aeval A p‖ ≤ 3 * polynomialSupNorm p (K n) := by
    intro n
    have hpos : (0 : ℝ) < r + 1 / ((n : ℝ) + 1) := by positivity
    refine norm_aeval_le_three_mul_polynomialSupNorm_closedBall_of_closure_numericalRange_subset_ball
      A hpos (hW.trans ?_) p
    intro z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds (hlim.const_mul 3) hbound
