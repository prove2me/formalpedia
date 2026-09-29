-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback
-- name    : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/d12ed8d3-a361-52d0-8a11-48a01ce94ec4
-- title:
--   Local freeness of rank n is stable under pullback
-- statement:
--   Let $X$ and $Y$ be schemes, let $\psi \colon X \to Y$ be a morphism of schemes, let $n$ be a natural number and let $E$ be a sheaf of $\mathcal{O}_Y$-modules. Assume that $E$ satisfies `IsLocallyFreeOfRank n`, that is: for every point $y$ of $Y$ there is an open subset $U \subseteq Y$ with $y \in U$ such that the pullback of $E$ along the inclusion $U \hookrightarrow Y$ (the functor `Scheme.Modules.pullback U.ι`) is isomorphic, as a sheaf of $\mathcal{O}_U$-modules, to the free sheaf on the index type `ULift (Fin n)` — the isomorphism being asserted only through the nonemptiness of the type of such isomorphisms. The conclusion is that the inverse image $(\mathrm{Scheme.Modules.pullback}\ \psi)(E) = \psi^{*}E$ satisfies the same predicate with the same $n$: every point of $X$ has an open neighbourhood on which $\psi^{*}E$ becomes isomorphic to the free sheaf of modules on `ULift (Fin n)`.
--
--   This is the standard fact that the inverse image of a locally free sheaf of rank $n$ is locally free of rank $n$, stated for the project's scheme-theoretic notion of local freeness. It is used in the treatment of determinants and of pushforwards of locally free modules, for instance by [`AlgebraicGeometry.Scheme.Modules.nonempty_pullback_det_iso_det_pullback`](thm.html#AlgebraicGeometry.Scheme.Modules.nonempty_pullback_det_iso_det_pullback), [`AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_of_isPullback`](thm.html#AlgebraicGeometry.Scheme.Modules.exists_iso_pullback_of_isPullback) and [`AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback`](thm.html#AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsLocallyFreeOfRank.pullback
    {X Y : Scheme.{u}} (ψ : X ⟶ Y) {n : ℕ} {E : Y.Modules}
    (hE : Scheme.Modules.IsLocallyFreeOfRank n E) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pullback ψ).obj E) := by sorry
