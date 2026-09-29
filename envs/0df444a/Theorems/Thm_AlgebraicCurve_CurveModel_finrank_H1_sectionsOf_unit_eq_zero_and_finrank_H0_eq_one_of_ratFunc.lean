-- Prove2me | Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc
-- name    : AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/8a7d7076-68b1-57d1-b33b-dcabb1b2258b
-- title:
--   Čech cohomology of mathcal O_C for a model of k(t)
-- statement:
--   Let $k$ be an algebraically closed field and let $M$ be a `CurveModel k (RatFunc k)`: a scheme $M.C$, integral, together with a morphism $M.toBase : M.C \to \operatorname{Spec} k$ that is proper and smooth of relative dimension $1$, a ring isomorphism of $\operatorname{RatFunc} k$ with the function field of $M.C$ carrying $\operatorname{algebraMap} k (\operatorname{RatFunc} k)$ to the germ at the generic point of the structure morphism, a bijection from the closed points of $M.C$ onto the places of $\operatorname{RatFunc} k$ over $k$ (valuation subrings containing $k$, proper, with principal ideals) matching each stalk, transported along that isomorphism, with the corresponding valuation subring, and the property that every finite set of points of $M.C$ lies in an affine open. Let $\mathcal W$ be a two-chart affine cover of $M.C$: affine opens $U_0, U_1$ with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine. Form the two-term Čech complex of $k$-modules $\Gamma(\mathcal O, U_0) \times \Gamma(\mathcal O, U_1) \to \Gamma(\mathcal O, U_0 \sqcap U_1)$, $(s_0,s_1) \mapsto s_1|_{U_0 \cap U_1} - s_0|_{U_0 \cap U_1}$, for the structure sheaf viewed as module over itself. Then its cokernel has $k$-dimension $0$, and its kernel has $k$-dimension $1$.
--
--   This is the statement that the projective line over an algebraically closed field has $\dim_k \check H^1(\mathcal W, \mathcal O) = 0$ and $\dim_k \check H^0(\mathcal W, \mathcal O) = 1$, in the two-chart Čech formulation used throughout the project's Euler-characteristic bookkeeping. It is the genus-zero input to the line-by-line Euler-characteristic computations on relative Picard groups and to the criterion recognising the unit module on a curve model of $k(t)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_CurveModel_finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicCurve

theorem AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc
    (k : Type u) [Field k] [IsAlgClosed k] (M : CurveModel k (RatFunc k)) (𝒲 : M.C.TwoAffineOpenCover) :
    Module.finrank k (𝒲.sectionsOf M.toBase (SheafOfModules.unit M.C.ringCatSheaf : M.C.Modules)).H1 = 0 ∧
      Module.finrank k (𝒲.sectionsOf M.toBase (SheafOfModules.unit M.C.ringCatSheaf : M.C.Modules)).H0 = 1 := by sorry
