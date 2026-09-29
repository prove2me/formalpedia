-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_valuationSubring_eq_of_isPrime_span_of_forall_aeval_mem
-- name    : AlgebraicCurve.TwoChartIntegralModel.valuationSubring_eq_of_isPrime_span_of_forall_aeval_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/e6217a43-0b25-59cd-aff4-88b7bbbe0f01
-- title:
--   Uniqueness of the valuation above an integral special fibre
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K_0$, and let $F$ be a field carrying compatible $R$- and $K_0$-algebra structures (so that $K_0$ is a subfield of $F$ over $R$). Let $j \in F$ be non-zero and transcendental over $R$, and assume $F$ is finite-dimensional and separable over the intermediate field $K_0(j) =$ `IntermediateField.adjoin K₀ {j}`. Write $A =$ `chartAlgFin R F j` for the subalgebra of $F$ consisting of the elements integral over $R[j] =$ `Algebra.adjoin R {j}`, i.e. the integral closure of $R[j]$ in $F$. Let $\varpi \in R$ be a prime element whose image generates a prime ideal of $A$. Let $V$ and $V'$ be valuation subrings of $F$ such that each contains the image of $R$, contains the image of $\varpi$ in its set of non-units `nonunits` (the maximal ideal), and satisfies: for every polynomial $P \in R[X]$ not divisible by the constant $\varpi$, both $P(j)$ and $P(j)^{-1}$ lie in the ring. Then $V = V'$.
--
--   This is the uniqueness counterpart to the existence of a valuation subring attached to a minimal prime of the special fibre: when $\varpi A$ is prime, so that the fibre at $\varpi$ of the finite chart of the two-chart integral model of $(F,j)$ over $R$ is integral, the Gauss valuation of $K_0(j)$ with respect to $j$ and $\varpi$ has exactly one extension to $F$. It is used in the identification of stalks and valuation subrings for the two-chart integral models of the modular curves $X_1(p)$ and $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_valuationSubring_eq_of_isPrime_span_of_forall_aeval_mem.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open AlgebraicCurve.TwoChartIntegralModel

theorem AlgebraicCurve.TwoChartIntegralModel.valuationSubring_eq_of_isPrime_span_of_forall_aeval_mem
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (hint : (Ideal.span {algebraMap R ↥(chartAlgFin R F j) ϖ}).IsPrime)
    (V V' : ValuationSubring F)
    (hRV : ∀ r : R, algebraMap R F r ∈ V) (hϖV : algebraMap R F ϖ ∈ V.nonunits)
    (hjV : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V)
    (hRV' : ∀ r : R, algebraMap R F r ∈ V') (hϖV' : algebraMap R F ϖ ∈ V'.nonunits)
    (hjV' : ∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
      Polynomial.aeval j P ∈ V' ∧ (Polynomial.aeval j P)⁻¹ ∈ V') :
    V = V' := by sorry
