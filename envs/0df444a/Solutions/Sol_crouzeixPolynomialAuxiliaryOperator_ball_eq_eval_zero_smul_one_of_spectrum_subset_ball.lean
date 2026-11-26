-- Prove2me | solution 1 for crouzeixPolynomialAuxiliaryOperator_ball_eq_eval_zero_smul_one_of_spectrum_subset_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:26.5675+00:00
-- url     : https://prove2.me/submissions/b5293112-39b3-4bdd-a629-8e27ab7a51b6

import Definitions.Def_Operator_Crouzeix_SpectralCauchy
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliary
import Theorems.Thm_Polynomial_aeval_affineComposition
import Theorems.Thm_Polynomial_eval_affineComposition
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_mem_resolventSet_of_notMem_ball_of_spectrum_subset
import Theorems.Thm_normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball
import Theorems.Thm_normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_spectrum_subset_ball
attribute [local simp] Polynomial.aeval_affineComposition
attribute [local simp] Polynomial.eval_affineComposition
attribute [local simp] mem_numericalRange


section
open Complex ComplexConjugate Polynomial Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
private theorem circleIntegrable_star_eval_smul_resolvent_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) (q : Polynomial ℂ) :
    CircleIntegrable (fun z => star (Polynomial.eval z q) • resolvent A z) 0 r := by
  apply ContinuousOn.circleIntegrable hr.le
  refine q.continuous.star.continuousOn.smul ?_
  intro z hz
  have hznot : z ∉ Metric.ball (0 : ℂ) r := by
    intro hzball
    rw [Metric.mem_ball] at hzball
    rw [Metric.mem_sphere] at hz
    rw [hz] at hzball
    exact (lt_irrefl r) hzball
  exact (spectrum.hasDerivAt_resolvent_const_left
    (mem_resolventSet_of_notMem_ball_of_spectrum_subset A hσ hznot)).continuousAt.continuousWithinAt
private theorem normalized_circleIntegral_resolvent_eq_one_of_spectrum_subset_ball
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) :
    (2 * (Real.pi : ℂ) * I)⁻¹ • circleIntegral (resolvent A) 0 r =
      (1 : E →L[ℂ] E) := by
  simpa only [Polynomial.eval_one, one_smul, map_one] using
    (normalized_circleIntegral_eval_smul_resolvent_eq_aeval_of_spectrum_subset_ball
      A hr hσ (1 : Polynomial ℂ))
end

set_option autoImplicit false
open Complex ComplexConjugate Polynomial Set spectrum
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) {r : ℝ} (hr : 0 < r)
    (hσ : spectrum ℂ A ⊆ Metric.ball (0 : ℂ) r) (p : Polynomial ℂ) :
    crouzeixPolynomialAuxiliaryOperator A (SmoothJordanDomain.ball 0 r hr) p =
      star (Polynomial.eval 0 p) • (1 : E →L[ℂ] E) := by
  have hcont (q : Polynomial ℂ) :
      CircleIntegrable (fun z => star (Polynomial.eval z q) • resolvent A z) 0 r :=
    circleIntegrable_star_eval_smul_resolvent_of_spectrum_subset_ball A hr hσ q
  have hresolvent :
      (2 * (Real.pi : ℂ) * I)⁻¹ • circleIntegral (resolvent A) 0 r =
        (1 : E →L[ℂ] E) :=
    normalized_circleIntegral_resolvent_eq_one_of_spectrum_subset_ball A hr hσ
  change (2 * (Real.pi : ℂ) * I)⁻¹ •
      circleIntegral (fun z => star (Polynomial.eval z p) • resolvent A z) 0 r = _
  -- Polynomial induction separates the constant Cauchy mode from the strictly
  -- negative Laurent modes obtained by conjugating every positive monomial.
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
        rw [← smul_smul, hresolvent]
        simp only [Polynomial.eval_monomial, pow_zero, mul_one]
      · let m := n + 1
        have hm : 0 < m := Nat.zero_lt_succ n
        have hintegral :
            circleIntegral
                (fun z => star (Polynomial.eval z (Polynomial.monomial m a)) • resolvent A z)
                0 r =
              circleIntegral
                (fun z => (star a * (r : ℂ) ^ (2 * m)) •
                  (z⁻¹ ^ m • resolvent A z)) 0 r := by
          apply circleIntegral.integral_congr hr.le
          intro z hz
          have hz' : z ∈ Metric.sphere (0 : ℂ) |r| := by
            simpa only [abs_of_pos hr] using hz
          rw [← range_circleMap] at hz'
          obtain ⟨t, rfl⟩ := hz'
          have hstar : star (circleMap 0 r t) =
              ((r : ℂ) ^ 2) * (circleMap 0 r t)⁻¹ := by
            change conj (circleMap 0 r t) = _
            rw [conj_circleMap_zero, circleMap_zero_inv]
            simp only [circleMap_zero, ofReal_neg, neg_mul, ofReal_inv]
            field_simp [Complex.ofReal_ne_zero.mpr hr.ne']
          change star (Polynomial.eval (circleMap 0 r t) (Polynomial.monomial m a)) •
              resolvent A (circleMap 0 r t) =
            (star a * (r : ℂ) ^ (2 * m)) •
              ((circleMap 0 r t)⁻¹ ^ m • resolvent A (circleMap 0 r t))
          rw [Polynomial.eval_monomial, star_mul, star_pow, hstar, mul_pow, smul_smul]
          rw [← pow_mul]
          congr 1
          ring
        rw [hintegral, circleIntegral.integral_smul, smul_smul]
        rw [show (2 * (Real.pi : ℂ) * I)⁻¹ * (star a * (r : ℂ) ^ (2 * m)) =
            (star a * (r : ℂ) ^ (2 * m)) * (2 * (Real.pi : ℂ) * I)⁻¹ by ring]
        rw [← smul_smul,
          normalized_circleIntegral_inv_pow_smul_resolvent_eq_zero_of_spectrum_subset_ball
            A hr hσ m hm, smul_zero]
        simp only [Polynomial.eval_monomial, m, zero_pow hm.ne', mul_zero, star_zero, zero_smul]
