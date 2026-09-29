-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_structureSheafSections_eq_finrank_span_germ
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_structureSheafSections_eq_finrank_span_germ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/a77dcd1e-b52c-547a-a1df-e373334f3402
-- title:
--   Two-chart Čech cohomology of 𝒪_C inside the function field
-- statement:
--   Let $k$ be a field, $C$ an integral scheme and $c : C \to \operatorname{Spec} k$ a morphism, and let $\mathcal{V}$ be a `TwoAffineOpenCover` of $C$, i.e. opens $U_0, U_1$ with $U_0$, $U_1$ and $U_0 \sqcap U_1$ affine and $U_0 \sqcup U_1 = \top$; assume the generic point $\eta$ of $C$ lies in $U_0$ (hypothesis `h0`) and in $U_1$ (hypothesis `h1`). The function field $\mathcal{O}_{C,\eta}$ is regarded as a $k$-algebra through [`AlgebraicCurve.baseToFunctionField c`](def/AlgebraicCurve_CurveModel.html#L18), the composite of the inverse of $\Gamma\!\operatorname{Spec}$-iso for $k$, the map on global sections induced by $c$, and the germ at $\eta$ of a global section. Write $V_U \subseteq \mathcal{O}_{C,\eta}$ for the $k$-span of the image of the germ map $\Gamma(C,U) \to \mathcal{O}_{C,\eta}$ at $\eta$. The assertion is a conjunction of two equalities of $k$-dimensions (in the sense of `Module.finrank`, so the infinite-dimensional case reads $0 = 0$) for the two-term Čech complex `(𝒱.structureSheafSections c)` attached to the chart rings $\Gamma(C,U_0)$, $\Gamma(C,U_1)$, $\Gamma(C, U_0 \sqcap U_1)$ and their restriction maps $r_0, r_1$: the dimension of its $H^0 = \ker\bigl((-r_0) \oplus r_1\bigr)$ equals that of $V_{U_0} \cap V_{U_1}$, and the dimension of its $H^1 = \Gamma(C, U_0 \sqcap U_1)/\operatorname{range}\bigl((-r_0) \oplus r_1\bigr)$ equals that of the quotient of $V_{U_0 \sqcap U_1}$ by the preimage in it of $V_{U_0} + V_{U_1}$, i.e. by $(V_{U_0} + V_{U_1}) \cap V_{U_0 \sqcap U_1}$.
--
--   This transports the two-chart Čech cohomology of the structure sheaf of an integral scheme into its function field, where the sections over the three charts appear as $k$-subspaces of $\mathcal{O}_{C,\eta}$ and $H^0$, $H^1$ become an intersection and a quotient of these subspaces. It is used in the estimate [`AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing`](thm.html#AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing) for the Euler characteristic of the structure sheaf in terms of the genus of the function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_structureSheafSections_eq_finrank_span_germ.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_structureSheafSections_eq_finrank_span_germ
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsIntegral C]
    (𝒱 : C.TwoAffineOpenCover) (h0 : genericPoint C ∈ 𝒱.U0) (h1 : genericPoint C ∈ 𝒱.U1) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.finrank k (𝒱.structureSheafSections c).H0 =
        Module.finrank k ↥(Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0) (genericPoint C) (h0)).hom) ⊓
          Submodule.span k (Set.range (C.presheaf.germ (𝒱.U1) (genericPoint C) (h1)).hom)) ∧
      Module.finrank k (𝒱.structureSheafSections c).H1 =
        Module.finrank k (↥(Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0 ⊓ 𝒱.U1) (genericPoint C) (⟨h0, h1⟩)).hom)) ⧸
          (Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0) (genericPoint C) (h0)).hom) ⊔ Submodule.span k (Set.range (C.presheaf.germ (𝒱.U1) (genericPoint C) (h1)).hom)).comap
            (Submodule.span k (Set.range (C.presheaf.germ (𝒱.U0 ⊓ 𝒱.U1) (genericPoint C) (⟨h0, h1⟩)).hom)).subtype) := by sorry
