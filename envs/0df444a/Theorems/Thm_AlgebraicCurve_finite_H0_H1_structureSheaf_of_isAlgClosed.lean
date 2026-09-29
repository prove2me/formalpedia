-- Prove2me | Theorems.Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed
-- name    : AlgebraicCurve.finite_H0_H1_structureSheaf_of_isAlgClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/c587555b-8ab0-55a5-98cc-36f66560d48e
-- title:
--   Čech h⁰=1 and h¹= genus for smooth proper curves
-- statement:
--   Let $K$ be an algebraically closed field and let $C$ be a scheme (in the same universe) which is integral, equipped with a morphism $c : C \to \operatorname{Spec} K$ that is proper and smooth of relative dimension $1$. Let $\mathcal V$ be a two-affine open cover of $C$: a pair of opens $U_0, U_1$, both affine, with $U_0 \sqcup U_1 = \top$ and with $U_0 \cap U_1$ affine. The associated two-term Čech complex has $M_0 = \Gamma(C, U_0)$, $M_1 = \Gamma(C, U_1)$, $M_{01} = \Gamma(C, U_0 \cap U_1)$ with the two restriction maps $r_0, r_1$, all regarded as $K$-modules through $c$; its differential is $(s_0,s_1) \mapsto r_1 s_1 - r_0 s_0$, and `H0`, `H1` are its kernel and the quotient of $M_{01}$ by its range. The function field $C.\text{functionField}$ (the stalk at the generic point) is a $K$-algebra via `baseToFunctionField`, the germ at the generic point of the map on global sections induced by $c$. The assertion is that `H0` and `H1` are finite $K$-modules, that $\operatorname{rank}_K$ `H0` $= 1$, and that $\operatorname{rank}_K$ `H1` equals `genusFF K C.functionField`, namely $\dim_K$ of the quotient of the algebra of repartitions of $C.\text{functionField}/K$ by the sum of the submodule of repartitions with $v$-valuation $\le 1$ at every place and the submodule of principal (constant) repartitions.
--
--   This is the statement $h^0(C,\mathcal O_C)=1$, $h^1(C,\mathcal O_C)=g$ for a smooth proper integral curve over an algebraically closed field, in the explicit two-chart Čech model and with the genus taken in its repartition (Weil) form for the function field. It is the hypothesis-free specialisation used downstream for base change of the Čech complex, for the comparison of $H^0$ of the Kähler sections with $H^1$ of the structure sheaf, and for the genus computation on the modular curve models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_finite_H0_H1_structureSheaf_of_isAlgClosed.lean

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

theorem AlgebraicCurve.finite_H0_H1_structureSheaf_of_isAlgClosed {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of K)) [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c] :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0 = 1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField := by sorry
