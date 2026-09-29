-- Prove2me | Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase
-- name    : AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/2625ae3e-f658-577a-b49c-b45884e1025e
-- title:
--   Discrete valuation through a point of the special fibre
-- statement:
--   Let $R$ be a principal ideal domain with fraction field $K_0$, let $F$ be a field equipped with $R$- and $K_0$-algebra structures forming a scalar tower, and let $j \in F$ be a nonzero element (its nonvanishing being registered as a hypothesis) that is transcendental over $R$, and such that $F$ is finite-dimensional and separable over the intermediate field $K_0(j) =$ `IntermediateField.adjoin K₀ {j}`. Write $A_{\mathrm{fin}} =$ `chartAlgFin R F j` for the subalgebra of elements of $F$ integral over $R[j] =$ `Algebra.adjoin R {j}`, and $A_\infty =$ `chartAlgInf R F j` for the elements integral over $R[j^{-1}]$; let $X_{\mathrm{fin}} = \operatorname{Spec} A_{\mathrm{fin}}$, $X_\infty = \operatorname{Spec} A_\infty$, and let `TwoChartIntegralModel R F j` be the pushout of the two morphisms `fFin`, `fInf` from the middle chart, with `ιFin`, `ιInf` the canonical morphisms of the charts into it and `toBase` the induced morphism to $\operatorname{Spec} R$. Let $\varpi \in R$ be prime and let $x$ be a point of the pushout whose image under `toBase` is a prime of $R$ containing $\varpi$. Then there is a valuation subring $V \subseteq F$ such that: $V$ is a discrete valuation ring; every element of $A_{\mathrm{fin}}$ and every element of $A_\infty$ lies in $V$; the image of $\varpi$ in $F$ is a non-unit of $V$; for every $P \in R[X]$ not divisible by the constant polynomial $\varpi$, both $P(j)$ and $P(j)^{-1}$ lie in $V$; and, for every prime $y$ of $A_{\mathrm{fin}}$ with `ιFin`$(y) = x$, every $b \in A_{\mathrm{fin}}$ that is a non-unit of $V$ lies in $y$, and likewise for every prime $y$ of $A_\infty$ with `ιInf`$(y) = x$ and every non-unit $b \in A_\infty$.
--
--   The statement produces, for a point of the fibre over $(\varpi)$ of the two-chart integral model of $(F,j)$ over $R$, a discrete valuation of $F$ centred at that point on each chart containing it, whose restriction to $R[j]$ is the Gauss valuation attached to $\varpi$ (so the corresponding component of the special fibre dominates the $j$-line). It refines `exists_valuationSubring_of_mem_minimalPrimes_chartAlgFin` from minimal primes of $(\varpi)$ to arbitrary points over $(\varpi)$, and feeds the construction of a normal proper model with prescribed valuation-theoretic behaviour.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_TwoChartIntegralModel_exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.TwoChartIntegralModel.exists_valuationSubring_forall_mem_nonunits_mem_asIdeal_of_mem_toBase
    (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (K₀ : Type u) [Field K₀] [Algebra R K₀] [IsFractionRing R K₀]
    (F : Type u) [Field F] [Algebra R F] [Algebra K₀ F] [IsScalarTower R K₀ F]
    (j : F) [Fact (j ≠ 0)] (htj : Transcendental R j)
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin K₀ ({j} : Set F)) F)
    (ϖ : R) (hϖ : Prime ϖ)
    (x : ↥(AlgebraicCurve.TwoChartIntegralModel R F j))
    (hx : ϖ ∈ ((AlgebraicCurve.TwoChartIntegralModel.toBase R F j).base x).asIdeal) :
    ∃ V : ValuationSubring F,
      IsDiscreteValuationRing ↥V ∧
      (∀ f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j), (f : F) ∈ V) ∧
      (∀ f : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j), (f : F) ∈ V) ∧
      algebraMap R F ϖ ∈ V.nonunits ∧
      (∀ P : Polynomial R, ¬ (Polynomial.C ϖ ∣ P) →
        Polynomial.aeval j P ∈ V ∧ (Polynomial.aeval j P)⁻¹ ∈ V) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XFin R F j), (AlgebraicCurve.TwoChartIntegralModel.ιFin R F j).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) ∧
      (∀ y : ↥(AlgebraicCurve.TwoChartIntegralModel.XInf R F j), (AlgebraicCurve.TwoChartIntegralModel.ιInf R F j).base y = x →
        ∀ b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf R F j), (b : F) ∈ V.nonunits → b ∈ y.asIdeal) := by sorry
