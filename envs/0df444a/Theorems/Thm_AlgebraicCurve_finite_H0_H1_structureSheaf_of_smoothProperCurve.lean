-- Prove2me | Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve
-- name    : AlgebraicCurve.finite_H0_H1_structureSheaf_of_smoothProperCurve
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/3236bbbc-b7ca-5959-8a75-f29da932441a
-- title:
--   Čech H⁰,H¹ of mathcal O_C on a two-affine cover
-- statement:
--   Let $K$ be a field and $C$ an integral scheme equipped with a morphism $c : C \to \operatorname{Spec} K$ that is proper and smooth of relative dimension $1$, together with a two-affine open cover $\mathcal V$ of $C$: opens $U_0,U_1$, both affine, with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. The function field $F =$ `C.functionField` is made a $K$-algebra through [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the composite of the inverse of $\Gamma\operatorname{Spec}$-adjunction iso, $c$ on global sections, and the germ map at the generic point. Three hypotheses are imposed on $F/K$: that [`AlgebraicCurve.IsCurveOver K F`](def/AlgebraicCurve_IsCurveOver.html#L15) holds, i.e. $F/K$ has principal divisors, every place of $F/K$ (a valuation subring $\neq F$ containing $K$ and a principal ideal ring) has residue field finite over $K$, and $\Omega_{F/K}$ is free of rank $1$ over $F$; that $L(0)$, the Riemann–Roch space of the zero divisor, is finite-dimensional over $K$; and that the Riemann bound is attained, i.e. there are $\gamma \in \mathbb Z$ and a divisor $D_0$ with $L(D_0)$ finite-dimensional, $\deg D_0 - \ell(D_0) = \gamma - 1$, and $\deg D - \ell(D) \le \gamma - 1$ for every divisor $D$. The conclusion: the Čech groups of the structure sheaf on $\mathcal V$ — the kernel $H^0$ and the cokernel $H^1$ of the difference map $\mathcal O(U_0) \times \mathcal O(U_1) \to \mathcal O(U_0 \cap U_1)$ — are finite $K$-modules, with $\dim_K H^0 = \ell(0)$ and $\dim_K H^1 =$ `genusFF K F`, the $K$-dimension of the répartition quotient $H^1(0)$.
--
--   This is the comparison, for a smooth proper integral curve over a field, between the Čech cohomology of $\mathcal O_C$ computed on a two-chart affine cover and the Riemann–Roch invariants of the function field: $h^0 = \ell(0)$ and $h^1$ equals the répartition genus. It feeds the corresponding statement over an algebraically closed base field, [`AlgebraicCurve.finite_H0_H1_structureSheaf_of_isAlgClosed`](thm.html#AlgebraicCurve.finite_H0_H1_structureSheaf_of_isAlgClosed).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_TwoChartCech
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicCurve_PlacesOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicCurve.finite_H0_H1_structureSheaf_of_smoothProperCurve {K : Type u} [Field K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (hcurve : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      AlgebraicCurve.IsCurveOver K C.functionField)
    (hL0 : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K C.functionField)))
    (hreach : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      ∃ (γ : ℤ) (D₀ : AlgebraicCurve.Divisor K C.functionField), AlgebraicCurve.RiemannGenusReachedAt γ D₀) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0
        = AlgebraicCurve.ell (0 : AlgebraicCurve.Divisor K C.functionField) ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField := by sorry
