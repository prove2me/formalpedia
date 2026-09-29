-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
-- name    : AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/728b1c88-4b7f-5793-971c-e0ab63a7b363
-- title:
--   Local freeness of a direct image is local on the base
-- statement:
--   Let $X$ and $T$ be schemes, $\pi \colon X \to T$ a morphism, $F$ an $\mathcal{O}_X$-module (an object of `X.Modules`), and $n$ a natural number. Assume that for every point $y$ of $T$ there are an open subscheme $W$ of $T$ with $y \in W$, schemes $W'$ and $X'$, an isomorphism $e \colon W' \cong W$, and morphisms $\pi' \colon X' \to W'$ and $g' \colon X' \to X$ such that the square with sides $g'$, $\pi'$, $\pi$ and $e$ followed by the open immersion $W \hookrightarrow T$ is cartesian, and such that $\pi'_*(g'^*F)$ is locally free of rank $n$ on $W'$, that is: every point of $W'$ has an open neighbourhood $U$ for which the restriction of $\pi'_*(g'^*F)$ along $U \hookrightarrow W'$ is isomorphic to the free module on $\mathrm{ULift}(\mathrm{Fin}\ n)$. The conclusion is that $\pi_*F$ is locally free of rank $n$ on $T$ in the same sense: every point of $T$ has an open neighbourhood $U$ such that the restriction of $\pi_*F$ along $U \hookrightarrow T$ is isomorphic to the free module on $\mathrm{ULift}(\mathrm{Fin}\ n)$.
--
--   This is the statement that local freeness of a fixed rank $n$ for a direct image $\pi_*F$ may be checked Zariski-locally on the base, after an arbitrary base change of the family along an isomorphic copy $W' \cong W$ of the open used; it combines the locality of local freeness with the compatibility of pushforward with restriction to an open of the base. It is the tool by which the relative Picard development reduces local freeness of a direct image to a computation on fibres or on members of an affine cover.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
    {X T : Scheme.{u}} (π : X ⟶ T) (F : X.Modules) (n : ℕ)
    (h : ∀ y : T, ∃ (W : T.Opens), y ∈ W ∧ ∃ (W' X' : Scheme.{u}) (e : W' ≅ W.toScheme) (π' : X' ⟶ W')
      (g' : X' ⟶ X), IsPullback g' π' π (e.hom ≫ W.ι) ∧
        Scheme.Modules.IsLocallyFreeOfRank n
          ((Scheme.Modules.pushforward π').obj ((Scheme.Modules.pullback g').obj F))) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward π).obj F) := by sorry
