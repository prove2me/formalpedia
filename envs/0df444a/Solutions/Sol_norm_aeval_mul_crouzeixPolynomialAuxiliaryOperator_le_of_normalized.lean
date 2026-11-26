-- Prove2me | solution 1 for norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_le_of_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:34:27.068732+00:00
-- url     : https://prove2.me/submissions/1462b862-b412-4f51-ad32-4c81b56b679c

import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Definitions.Def_Operator_Crouzeix_ProductNormalization
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_polynomialSupNorm_smul
import Theorems.Thm_polynomial_eq_zero_of_polynomialSupNorm_eq_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (K : Set ℂ)
    (hK : IsCompact K) (hKinf : K.Infinite) (p : Polynomial ℂ)
    (hp : 0 < p.natDegree)
    (hnormalized : ∀ q : Polynomial ℂ, 0 < q.natDegree →
      polynomialSupNorm q K = 1 →
        ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
      polynomialSupNorm p K ^ 2 := by
  let m := polynomialSupNorm p K
  have hm0 : m ≠ 0 := by
    intro hm
    have hpzero : p = 0 :=
      polynomial_eq_zero_of_polynomialSupNorm_eq_zero p hK hKinf hm
    subst p
    simp only [Polynomial.natDegree_zero, lt_self_iff_false] at hp
  have hm : 0 < m :=
    lt_of_le_of_ne (polynomialSupNorm_nonneg p K) (Ne.symm hm0)
  let q : Polynomial ℂ := ((m : ℂ)⁻¹) • p
  have hscalar : ((m : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr hm0)
  have hqdegree : 0 < q.natDegree := by
    dsimp only [q]
    rw [Polynomial.natDegree_smul p hscalar]
    exact hp
  have hqnorm : polynomialSupNorm q K = 1 := by
    dsimp only [q]
    rw [polynomialSupNorm_smul]
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    exact inv_mul_cancel₀ hm0
  have hqbound := hnormalized q hqdegree hqnorm
  have hpq : (m : ℂ) • q = p := by
    dsimp only [q]
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hm0), one_smul]
  calc
    ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ =
        m ^ 2 * ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ := by
      rw [← hpq, norm_aeval_mul_crouzeixPolynomialAuxiliaryOperator_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hm]
    _ ≤ m ^ 2 * 1 := mul_le_mul_of_nonneg_left hqbound (sq_nonneg m)
    _ = polynomialSupNorm p K ^ 2 := by simp only [m, mul_one]
