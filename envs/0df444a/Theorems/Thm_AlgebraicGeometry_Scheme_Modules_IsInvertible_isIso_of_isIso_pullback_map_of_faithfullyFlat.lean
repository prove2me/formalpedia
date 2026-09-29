-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullback_map_of_faithfullyFlat
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_isIso_pullback_map_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/38319d28-ca7c-57a6-998f-f82029feb916
-- title:
--   Faithfully flat base change reflects isomorphisms of invertible modules
-- statement:
--   Let $S$ and $S'$ be commutative rings with $S'$ an $S$-algebra that is faithfully flat as an $S$-module. Let $X, X'$ be schemes, $f : X \to \operatorname{Spec} S$, $f' : X' \to \operatorname{Spec} S'$ morphisms and $c : X' \to X$ a morphism such that the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ is cartesian (`IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S')))`). Let $L$ and $M$ be $\mathcal O_X$-modules (objects of `X.Modules`), each assumed invertible in the sense of `Scheme.Modules.IsInvertible`: for every point $x$ of $X$ there is an open $U \subseteq X$ containing $x$ such that the pullback of the module along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module $\mathcal O_U$ on $U$. Let $\theta : L \to M$ be a morphism of $\mathcal O_X$-modules whose pullback $(\mathrm{Scheme.Modules.pullback}\ c).map\ \theta$, a morphism of $\mathcal O_{X'}$-modules, is an isomorphism. Then $\theta$ is itself an isomorphism.
--
--   This is the descent statement that an fpqc (here: affine faithfully flat) base change reflects isomorphisms between invertible modules. It is used to transfer isomorphy of line bundles back along a faithfully flat extension of the affine base, in particular by [`AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_restrict_of_isIso_restrict_pullback_of_faithfullyFlat`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_restrict_of_isIso_restrict_pullback_of_faithfullyFlat) and by the statement that an isomorphism of invertible modules exists after base change only if one exists already, over a local ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_of_isIso_pullback_map_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_of_isIso_pullback_map_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (θ : L ⟶ M) (hθ : IsIso ((Scheme.Modules.pullback c).map θ)) :
    IsIso θ := by sorry
