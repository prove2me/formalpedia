-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:08.464323+00:00
-- url     : https://prove2.me/submissions/4427c9ba-fedf-4d13-969f-80684fa5ca63

import Definitions.Def_Operator_Crouzeix_AuxOperator
import Definitions.Def_Operator_Crouzeix_CircleCauchy
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Theorems.Thm_crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_le_of_mem_numericalRange
import Theorems.Thm_normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero
import Theorems.Thm_normalized_circleIntegral_resolvent_eq_one
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex ComplexConjugate Polynomial Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {R : ℝ} (hR : ‖A‖ < R) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A
        (SmoothJordanDomain.ball 0 R ((norm_nonneg A).trans_lt hR)) p =
      star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E) := by
  have hRpos : 0 < R := (norm_nonneg A).trans_lt hR
  have hW : closure (numericalRange A) ⊆ Metric.ball (0 : ℂ) R := by
    have hsub : numericalRange A ⊆ Metric.closedBall (0 : ℂ) ‖A‖ := fun z hz => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact norm_le_of_mem_numericalRange A hz
    exact (closure_minimal hsub Metric.isClosed_closedBall).trans
      (Metric.closedBall_subset_ball hR)
  have hcont (q : Polynomial ℂ) :
      CircleIntegrable (fun z => star (Polynomial.eval z q) • resolvent A z) 0 R := by
    apply (circleIntegrable_iff R).mpr
    exact crouzeixPolynomialAuxiliaryIntegrand_contourIntegrable A
      (SmoothJordanDomain.ball 0 R hRpos) q hW
  change (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z => star (Polynomial.eval z p) • resolvent A z) 0 R = _
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hfun :
          (fun z => star (Polynomial.eval z (p + q)) • resolvent A z) =
            fun z => star (Polynomial.eval z p) • resolvent A z +
              star (Polynomial.eval z q) • resolvent A z := by
        funext z
        rw [Polynomial.eval_add, star_add, add_smul]
      rw [hfun, circleIntegral.integral_add (hcont p) (hcont q), smul_add, hp, hq,
        Polynomial.eval_add, star_add, add_smul]
  | monomial n a =>
      obtain rfl | n := n
      · have hfun :
            (fun z => star (Polynomial.eval z (Polynomial.monomial 0 a)) • resolvent A z) =
              fun z => star a • resolvent A z := by
          funext z
          rw [Polynomial.eval_monomial, pow_zero, mul_one]
        rw [hfun, circleIntegral.integral_smul, smul_smul]
        rw [show (2 * (Real.pi : ℂ) * I)⁻¹ * star a =
            star a * (2 * (Real.pi : ℂ) * I)⁻¹ by ring]
        rw [← smul_smul, normalized_circleIntegral_resolvent_eq_one A hR]
        simp only [Polynomial.eval_monomial, pow_zero, mul_one]
      · let m := n + 1
        have hm : 0 < m := Nat.zero_lt_succ n
        have hintegral :
            circleIntegral
                (fun z => star (Polynomial.eval z (Polynomial.monomial m a)) • resolvent A z)
                0 R =
              circleIntegral
                (fun z => (star a * (R : ℂ) ^ (2 * m)) •
                  (z⁻¹ ^ m • resolvent A z)) 0 R := by
          apply circleIntegral.integral_congr hRpos.le
          intro z hz
          have hz' : z ∈ Metric.sphere (0 : ℂ) |R| := by
            simpa only [abs_of_pos hRpos] using hz
          rw [← range_circleMap] at hz'
          obtain ⟨t, rfl⟩ := hz'
          have hstar : star (circleMap 0 R t) =
              ((R : ℂ) ^ 2) * (circleMap 0 R t)⁻¹ := by
            change conj (circleMap 0 R t) = _
            rw [conj_circleMap_zero, circleMap_zero_inv]
            simp only [circleMap_zero, ofReal_neg, neg_mul, ofReal_inv]
            field_simp [Complex.ofReal_ne_zero.mpr hRpos.ne']
          change star (Polynomial.eval (circleMap 0 R t) (Polynomial.monomial m a)) •
              resolvent A (circleMap 0 R t) =
            (star a * (R : ℂ) ^ (2 * m)) •
              ((circleMap 0 R t)⁻¹ ^ m • resolvent A (circleMap 0 R t))
          rw [Polynomial.eval_monomial, star_mul, star_pow, hstar, mul_pow, smul_smul]
          rw [← pow_mul]
          congr 1
          ring
        rw [hintegral, circleIntegral.integral_smul, smul_smul]
        rw [show (2 * (Real.pi : ℂ) * I)⁻¹ * (star a * (R : ℂ) ^ (2 * m)) =
            (star a * (R : ℂ) ^ (2 * m)) * (2 * (Real.pi : ℂ) * I)⁻¹ by ring]
        rw [← smul_smul,
          normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero A hR m hm, smul_zero]
        simp only [Polynomial.eval_monomial, m, zero_pow hm.ne', mul_zero, star_zero, zero_smul]
