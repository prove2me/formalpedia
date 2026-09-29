-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_linearEquiv_H1_sectionsOf_of_isSeparated
-- name    : AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/62632504-fd80-5397-ac9b-4eafea60df4a
-- title:
--   Two-chart Čech H¹ is independent of the chart pair
-- statement:
--   Let $R$ be a commutative ring and let $c\colon X \to \operatorname{Spec} R$ be a morphism of schemes which is separated, and let $M$ be a sheaf of $\mathcal{O}_X$-modules on $X$ (an object of `X.Modules`). Assume $M$ is locally trivial in the following sense: for every point $x$ of $X$ there is an open $W \subseteq X$ with $x \in W$ such that the pullback of $M$ along the open immersion $W \hookrightarrow X$ is isomorphic, as a sheaf of modules over the structure sheaf of $W$, to the unit object (the structure sheaf itself). Let $\mathcal{V}$ and $\mathcal{V}'$ be two data of the form: opens $U_0, U_1$ of $X$ with $U_0$, $U_1$ and $U_0 \sqcap U_1$ affine and $U_0 \sqcup U_1 = \top$. To such a datum $\mathcal{V}$ is attached the two-chart Čech system of $M$ over $c$: the $R$-modules $\Gamma(M, U_0)$, $\Gamma(M, U_1)$, $\Gamma(M, U_0 \sqcap U_1)$, each an $R$-module through the algebra map $R \to \Gamma(X, U)$ coming from $c$, together with the two restriction maps $r_0, r_1$ to $\Gamma(M, U_0 \sqcap U_1)$, and $H^1$ is the quotient of $\Gamma(M, U_0 \sqcap U_1)$ by the image of the $R$-linear map $(m_0, m_1) \mapsto -r_0 m_0 + r_1 m_1$. The conclusion is that the type of $R$-linear equivalences between the $H^1$ attached to $\mathcal{V}$ and the $H^1$ attached to $\mathcal{V}'$ is nonempty; no particular isomorphism is singled out.
--
--   This is the cover-independence of Čech cohomology for quasi-coherent (here locally free of rank one) sheaves, in the degree-one, two-chart form used throughout the project's treatment of relative Picard groups; it rests on the vanishing of the relevant Čech cohomology over affine opens, the mixed intersections being affine because $c$ is separated. It is used in the statements about Euler characteristics and ranks of $H^1$ in fibres of families of curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_linearEquiv_H1_sectionsOf_of_isSeparated.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.nonempty_linearEquiv_H1_sectionsOf_of_isSeparated
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) [IsSeparated c]
    (M : X.Modules)
    (htriv : ∀ x : X, ∃ W : X.Opens, x ∈ W ∧
      Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit W.toScheme.ringCatSheaf))
    (𝒱 𝒱' : X.TwoAffineOpenCover) :
    Nonempty ((𝒱.sectionsOf c M).H1 ≃ₗ[R] (𝒱'.sectionsOf c M).H1) := by sorry
