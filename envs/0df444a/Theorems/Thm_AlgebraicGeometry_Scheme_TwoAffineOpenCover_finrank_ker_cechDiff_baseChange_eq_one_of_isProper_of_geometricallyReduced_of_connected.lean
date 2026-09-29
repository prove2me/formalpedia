-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one_of_isProper_of_geometricallyReduced_of_connected
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_ker_cechDiff_baseChange_eq_one_of_isProper_of_geometricallyReduced_of_connected
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/b7f4852e-2c00-55b1-b197-82d44cc66530
-- title:
--   h⁰ = 1 on field fibres of a proper flat family
-- statement:
--   Let $R$ be a Noetherian commutative ring, $X$ a scheme, and $\mathcal V$ a two-affine open cover of $X$: a pair of open subschemes $U_0, U_1$, both affine, with $U_0 \sqcup U_1 = \top$ and $U_0 \sqcap U_1$ affine as well. Let $c \colon X \to \operatorname{Spec} R$ be a proper flat morphism. Assume that for every algebraically closed field $L$ equipped with an $R$-algebra structure, the fibre product of $c$ with $\operatorname{Spec}$ of the structure map $R \to L$ is a reduced scheme with connected underlying topological space. Let $K$ be any field with an $R$-algebra structure. Write $S$ for the `Sections` datum `structureSheaf` attached to the cover $(\Gamma(X,U_0), \Gamma(X,U_1), \Gamma(X, U_0 \sqcap U_1))$ determined by $\mathcal V$ and $c$, and let $d = \mathrm{cechDiff}$ be the $R$-linear map $S.M_0 \times S.M_1 \to S.M_{01}$ sending $(m_0,m_1)$ to $-r_0(m_0) + r_1(m_1)$, the difference of the two restriction maps. The conclusion is that the kernel of the base-changed map $d \otimes_R K$, from $K \otimes_R (S.M_0 \times S.M_1)$ to $K \otimes_R S.M_{01}$, has $K$-dimension exactly $1$.
--
--   This is the statement that the zeroth Čech cohomology of the structure sheaf has rank one on every field-valued fibre of a proper flat family whose geometric fibres are reduced and connected, computed through a two-chart Čech complex. It is the form in which $h^0 = 1$ is used downstream, for instance in identifying $c_*\mathcal O_X$ with the base ring after base change for Deligne–Rapoport models of modular curves, and in the comparison of the Kähler $H^0$ with the structure-sheaf $H^1$ for relatively one-dimensional smooth families.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_ker_cechDiff_baseChange_eq_one_of_isProper_of_geometricallyReduced_of_connected.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_ker_cechDiff_baseChange_eq_one_of_isProper_of_geometricallyReduced_of_connected
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [IsProper c] [Flat c]
    (hred : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      IsReduced (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R L)))
    (hconn : ∀ (L : Type u) [Field L] [IsAlgClosed L] [Algebra R L],
      ConnectedSpace ↥(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R L)))
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) = 1 := by sorry
