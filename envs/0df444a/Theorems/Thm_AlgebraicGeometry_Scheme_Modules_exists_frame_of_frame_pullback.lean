-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback
-- name    : AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/9f5d57af-7618-5236-aa9d-a50d0cde0d0a
-- title:
--   Descending a local frame along a morphism of schemes
-- statement:
--   Let $p\colon X'\to X$ be a morphism of schemes, let $M$ be a sheaf of modules on $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback of $M$ along the inclusion $U\hookrightarrow X$ is isomorphic to the unit module $\mathcal{O}_U$ (the predicate `Scheme.Modules.IsInvertible`), let $m\in\Gamma(M,\top)$ be a global section, and let $z$ be a point of $X'$. Write $p^{*}m\in\Gamma((\text{pullback }p)(M),\top)$ for the image of $m$ under the component at $\top$ of the unit of the adjunction `Scheme.Modules.pullbackPushforwardAdjunction p`. Assume that $p^{*}m$ is a frame of the pulled-back module near $z$: there is an open $U'\subseteq X'$ with $z\in U'$ such that for every open $V'\le U'$ the map $\Gamma(X',V')\to\Gamma((\text{pullback }p)(M),V')$, $g\mapsto g\cdot (p^{*}m)|_{V'}$, is bijective. The conclusion is that $m$ is then a frame of $M$ near $p(z)$: there is an open $U\subseteq X$ with $p(z)\in U$ such that for every open $V\le U$ the map $\Gamma(X,V)\to\Gamma(M,V)$, $g\mapsto g\cdot m|_{V}$, is bijective. No hypothesis is imposed on the morphism $p$.
--
--   This is the statement that the property of a global section of an invertible module being a local generator (a local frame) descends along an arbitrary morphism of schemes, the point being that the local homomorphism $\mathcal{O}_{X,p(z)}\to\mathcal{O}_{X',z}$ reflects units. It is used in the construction of frames for rigidified line bundles on relative Picard data, being cited in the passage from frames on geometric fibres and on basic opens to frames on the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback
    {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (m : Γ(M, ⊤)) (z : X')
    (h : ∃ U' : X'.Opens, z ∈ U' ∧ ∀ V' : X'.Opens, V' ≤ U' →
      Function.Bijective fun g : Γ(X', V') =>
        g • (((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) m) :
            Γ((Scheme.Modules.pullback p).obj M, V'))) :
    ∃ U : X.Opens, p z ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(M, V)) := by sorry
