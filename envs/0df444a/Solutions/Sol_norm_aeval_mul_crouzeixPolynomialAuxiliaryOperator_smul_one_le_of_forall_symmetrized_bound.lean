-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul_one_le_of_forall_symmetrized_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:34:28.78066+00:00
-- url     : https://prove2.me/submissions/404d64b0-feee-43e9-961a-e5af62ab6f67

import Definitions.Def_Operator_Crouzeix_NormalProduct
import Definitions.Def_Operator_Crouzeix_ProductSymmetrizedAlignment
import Theorems.Thm_circle_center_eq_scalar_of_forall_crouzeix_symmetrized_bound
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal
attribute [local simp] mem_numericalRange


section
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
omit [CompleteSpace E] in
private theorem numericalRange_smul_one_productAlignment (a : ℂ) :
    numericalRange (a • (1 : E →L[ℂ] E)) = {a} := by
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ :=
      (mem_numericalRange (a • (1 : E →L[ℂ] E)) _).mp hz
    rw [smul_apply, one_apply_eq_self, inner_smul_right,
      Set.mem_singleton_iff, inner_self_eq_norm_sq_to_K, hx]
    norm_num
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    obtain ⟨x, hx⟩ : (Metric.sphere (0 : E) 1).Nonempty :=
      NormedSpace.sphere_nonempty.mpr zero_le_one
    have hxnorm : ‖x‖ = 1 := by
      rw [Metric.mem_sphere, dist_zero_right] at hx
      exact hx
    apply (mem_numericalRange (a • (1 : E →L[ℂ] E)) a).mpr
    refine ⟨x, hxnorm, ?_⟩
    rw [smul_apply, one_apply_eq_self, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
end

set_option autoImplicit false
open Complex Polynomial Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
theorem _root_.solution
    (a c : ℂ) {R : ℝ}
    (hA : ‖a • (1 : E →L[ℂ] E) - c • 1‖ < R)
    (hsymm : ∀ q : Polynomial ℂ,
      ‖Polynomial.aeval (a • (1 : E →L[ℂ] E)) q +
          star (crouzeixPolynomialAuxiliaryOperator
            (a • (1 : E →L[ℂ] E))
            (SmoothJordanDomain.ball c R
              ((norm_nonneg (a • (1 : E →L[ℂ] E) - c • 1)).trans_lt hA)) q)‖ ≤
        2 * polynomialSupNorm q
          (closure (numericalRange (a • (1 : E →L[ℂ] E)))))
    (p : Polynomial ℂ) :
    ‖Polynomial.aeval (a • (1 : E →L[ℂ] E)) p *
        crouzeixPolynomialAuxiliaryOperator
          (a • (1 : E →L[ℂ] E))
          (SmoothJordanDomain.ball c R
            ((norm_nonneg (a • (1 : E →L[ℂ] E) - c • 1)).trans_lt hA)) p‖ ≤
      polynomialSupNorm p
        (closure (numericalRange (a • (1 : E →L[ℂ] E)))) ^ 2 := by
  have hca : c = a :=
    circle_center_eq_scalar_of_forall_crouzeix_symmetrized_bound
      a c hA hsymm
  subst c
  apply
    norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_ball_center_le_of_isStarNormal
      (a • (1 : E →L[ℂ] E)) a hA
  rw [numericalRange_smul_one_productAlignment a, closure_singleton]
  exact Set.mem_singleton a
