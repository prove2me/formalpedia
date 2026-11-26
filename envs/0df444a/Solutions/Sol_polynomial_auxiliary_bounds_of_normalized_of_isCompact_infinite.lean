-- Prove2me | solution 1 for polynomial_auxiliary_bounds_of_normalized_of_isCompact_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:37:05.652389+00:00
-- url     : https://prove2.me/submissions/8a536715-b79c-4c1d-b51b-6f69091f3c41

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.DiscreteSubset
import Definitions.Def_Operator_Crouzeix_PolynomialSupNormZero
import Theorems.Thm_polynomial_eq_zero_of_polynomialSupNorm_eq_zero
import Theorems.Thm_crouzeixPolynomialAuxiliaryOperator_smul
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_polynomialSupNorm_nonneg
import Theorems.Thm_polynomial_auxiliary_bounds_of_normalized
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Polynomial ContinuousLinearMap
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
theorem _root_.solution
    (A : H →L[ℂ] H) (Omega : SmoothJordanDomain) (K : Set ℂ)
    (hK : IsCompact K) (hKinf : K.Infinite) (p : Polynomial ℂ)
    (hnormalized : ∀ q : Polynomial ℂ,
      polynomialSupNorm q K = 1 →
        ‖Polynomial.aeval A q +
          star (crouzeixPolynomialAuxiliaryOperator A Omega q)‖ ≤ 2 ∧
        ‖Polynomial.aeval A q *
          crouzeixPolynomialAuxiliaryOperator A Omega q‖ ≤ 1) :
    ‖Polynomial.aeval A p +
        star (crouzeixPolynomialAuxiliaryOperator A Omega p)‖ ≤
          2 * polynomialSupNorm p K ∧
      ‖Polynomial.aeval A p *
        crouzeixPolynomialAuxiliaryOperator A Omega p‖ ≤
          polynomialSupNorm p K ^ 2 := by
  by_cases hm : polynomialSupNorm p K = 0
  · have hp : p = 0 :=
      polynomial_eq_zero_of_polynomialSupNorm_eq_zero p hK hKinf hm
    subst p
    have haux : crouzeixPolynomialAuxiliaryOperator A Omega 0 = 0 := by
      calc
        crouzeixPolynomialAuxiliaryOperator A Omega 0 =
            crouzeixPolynomialAuxiliaryOperator A Omega (0 • (1 : Polynomial ℂ)) := by
              rw [zero_smul]
        _ = star (0 : ℂ) •
            crouzeixPolynomialAuxiliaryOperator A Omega 1 :=
              crouzeixPolynomialAuxiliaryOperator_smul A Omega 0 1
        _ = 0 := by simp only [star_zero, zero_smul]
    rw [map_zero, haux, star_zero, add_zero, norm_zero, hm, mul_zero]
    constructor <;> norm_num
  · exact polynomial_auxiliary_bounds_of_normalized A Omega
      K p
      (lt_of_le_of_ne (polynomialSupNorm_nonneg p _) (Ne.symm hm)) hnormalized
