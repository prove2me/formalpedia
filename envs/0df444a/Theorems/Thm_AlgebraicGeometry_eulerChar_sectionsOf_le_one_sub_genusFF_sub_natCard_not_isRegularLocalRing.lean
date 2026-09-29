-- Prove2me | Theorems.Thm_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing
-- name    : AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/b6f7976c-186e-5a5f-ba65-97ad786dbd5a
-- title:
--   Čech Euler characteristic bounded by genus minus singularities
-- statement:
--   Let $k$ be an algebraically closed field, and let $c \colon C \to \operatorname{Spec} k$ be a proper morphism from an integral scheme $C$. Let $F$ be a field with a $k$-algebra structure, and let $M$ be a `CurveModel` for $F$ over $k$: a scheme $M.C$ with a proper, smooth of relative dimension $1$ structure morphism $M.\mathrm{toBase} \colon M.C \to \operatorname{Spec} k$ from an integral scheme, together with a ring isomorphism $F \cong M.C$'s function field compatible with $k$, a bijection between the closed points of $M.C$ and the places of $F/K$ (valuation subrings of $F$ containing $k$, proper, with principal ideals) matching each stalk with the corresponding valuation subring, and the property that every finite set of points of $M.C$ lies in an affine open. Let $\nu \colon M.C \to C$ satisfy $\nu$ followed by $c$ equals $M.\mathrm{toBase}$, and assume the stalk map of $\nu$ at the generic point of $M.C$ is an isomorphism. Let $\mathcal{V}$ consist of two affine opens $U_0, U_1$ of $C$ covering $C$ and with $U_0 \cap U_1$ affine. Form the two-term Čech complex of $k$-modules $\Gamma(U_0,\mathcal{O}_C) \times \Gamma(U_1,\mathcal{O}_C) \to \Gamma(U_0 \cap U_1,\mathcal{O}_C)$ given by the difference of restrictions, with $H^0$ its kernel and $H^1$ its cokernel. Then, as integers, $\dim_k H^0 - \dim_k H^1 \le 1 - g - n$, where $g$ is $\dim_k$ of the repartition quotient $\mathbb{A}_F/(\mathbb{A}_F(0)+F)$ defining `genusFF k F`, and $n$ is the cardinality (as `Nat.card`, hence $0$ if the set is infinite) of the set of points $z \in C$ whose local ring $\mathcal{O}_{C,z}$ is not regular.
--
--   This is the inequality $p_a(C) \ge g(F) + \#\operatorname{Sing}(C)$ for a proper integral curve $C$ with function field $F$ and normalisation $\nu \colon M.C \to C$, expressed through the Euler characteristic of the two-chart Čech complex of $\mathcal{O}_C$: each non-regular local ring contributes at least $1$ to the difference between arithmetic and geometric genus. It strengthens the corresponding bound $\le 1 - g$ without the singularity term, and is used by [`AlgebraicGeometry.eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing`](thm.html#AlgebraicGeometry.eulerChar_sectionsOf_le_sub_genusFF_sub_natCard_not_isRegularLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing
    (k : Type u) [Field k] [IsAlgClosed k]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsProper c] [IsIntegral C]
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase)
    (hbir : IsIso (ν.stalkMap (genericPoint M.C)))
    (𝒱 : C.TwoAffineOpenCover) :
    (Module.finrank k (𝒱.sectionsOf c (SheafOfModules.unit C.ringCatSheaf)).H0 : ℤ) -
        Module.finrank k (𝒱.sectionsOf c (SheafOfModules.unit C.ringCatSheaf)).H1 ≤
      1 - (AlgebraicCurve.genusFF k F : ℤ) - (Nat.card {z : C // ¬ IsRegularLocalRing (C.presheaf.stalk z)} : ℤ) := by sorry
