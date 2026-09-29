-- Prove2me | Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_locallyOfFiniteType_quasiCompact_isSeparated_of_universal_supportedIn
-- name    : AlgebraicGeometry.RelEffCartierDiv.locallyOfFiniteType_quasiCompact_isSeparated_of_universal_supportedIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.810897+00:00
-- url     : https://prove2.me/theorems/beae8e64-81ce-547d-b51e-0509547a5b99
-- title:
--   Representing scheme of divisors supported in U is of finite type, quasi-compact, separated
-- statement:
--   Let $f\colon\mathcal C\to S$ be a separated morphism of schemes with $S$ locally Noetherian, and let $U\subseteq\mathcal C$ be an open subscheme whose composite structure morphism $U\hookrightarrow\mathcal C\to S$ is smooth of relative dimension $1$ and quasi-compact. Fix $r\in\mathbb N$ and a morphism $y\colon Y\to S$, together with a relative effective Cartier divisor $\mathcal D_{\mathrm{univ}}$ of degree $r$ for $f$ over $y$, that is, an ideal sheaf datum $I$ on $\mathcal C\times_S Y$ whose associated closed subscheme maps to $Y$ by a morphism that is finite, flat and locally of finite presentation and has fibre rank exactly $r$ at every point of $Y$; assume $\mathcal D_{\mathrm{univ}}$ is supported in $U$, meaning that the support of $I$ is contained in the preimage of $U$ under the first projection. Assume further that $\mathcal D_{\mathrm{univ}}$ is universal among such data: for every scheme $T$, every $g\colon T\to S$ and every relative effective Cartier divisor $D$ of degree $r$ for $f$ over $g$ whose support lies over $U$, there is a unique pair consisting of $\varphi\colon T\to Y$ with $\varphi\circ\, y=g$ (composition in diagrammatic order) such that the comap of $I$ along the induced map $\mathcal C\times_S T\to\mathcal C\times_S Y$ equals the ideal sheaf datum of $D$. Then $y$ is locally of finite type, quasi-compact and separated.
--
--   This records the finiteness properties of a scheme representing the functor of degree-$r$ relative effective divisors supported in a smooth quasi-compact open chart of a curve over $S$, the object playing the role of $\mathrm{Div}^r$ or of a symmetric power. It is used in the construction of relative Picard schemes and their zero-cut descriptions for families of curves with two glued smooth degenerations and for two line degenerations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_RelEffCartierDiv_locallyOfFiniteType_quasiCompact_isSeparated_of_universal_supportedIn.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivRestrict

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelEffCartierDiv

theorem AlgebraicGeometry.RelEffCartierDiv.locallyOfFiniteType_quasiCompact_isSeparated_of_universal_supportedIn
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] [IsLocallyNoetherian S] (U : 𝒞.Opens)
    [SmoothOfRelativeDimension 1 (U.ι ≫ f)] [QuasiCompact (U.ι ≫ f)] (r : ℕ)
    {Y : Scheme.{u}} (y : Y ⟶ S) (Duniv : RelEffCartierDiv f r y) (hDunivU : Duniv.SupportedIn U)
    (huniv : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (D : RelEffCartierDiv f r g), D.SupportedIn U →
      ∃! φ : {φ : T ⟶ Y // φ ≫ y = g}, PullsBackOver Duniv φ.1 φ.2 D) :
    LocallyOfFiniteType y ∧ QuasiCompact y ∧ IsSeparated y := by sorry
