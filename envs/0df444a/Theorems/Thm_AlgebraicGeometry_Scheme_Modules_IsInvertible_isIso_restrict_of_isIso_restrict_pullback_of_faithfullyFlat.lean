-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_restrict_of_isIso_restrict_pullback_of_faithfullyFlat
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_restrict_of_isIso_restrict_pullback_of_faithfullyFlat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/eb019cbf-5498-51c4-ab71-6eb6a8a88be1
-- title:
--   Faithfully flat descent of isomorphy for invertible modules over an open
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra which is faithfully flat as an $S$-module. Let $X, X'$ be schemes, $f : X \to \operatorname{Spec} S$, $f' : X' \to \operatorname{Spec} S'$ and $c : X' \to X$ morphisms such that the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ is cartesian, i.e. $X'$ is the fibre product of $X$ and $\operatorname{Spec} S'$ over $\operatorname{Spec} S$. Let $L$ and $M$ be modules on $X$, each invertible in the sense that every point of $X$ has an open neighbourhood $U$ for which the pullback along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module of the sheaf of rings of $U$. Let $\theta : L \to M$ be a morphism of modules on $X$ and $W$ an open subscheme of $X$. Assume that the pullback of $\theta$ along $c$, further pulled back along the inclusion of $c^{-1}W$ into $X'$, is an isomorphism. Then the pullback of $\theta$ along the inclusion $W \hookrightarrow X$, that is the restriction $\theta|_W$, is an isomorphism.
--
--   This is the local-on-the-source form of faithfully flat descent of isomorphy for morphisms of invertible modules: isomorphy of $\theta$ over an open $W$ is detected after the faithfully flat base change $S \to S'$ of the affine base, restricted to the preimage of $W$. It is used in the construction of the relative Picard functor and its rigidifications, being cited by [`AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated`](thm.html#AlgebraicGeometry.Polarisation.LocIsoOnBase.of_pullback_of_faithfullyFlat_of_isSeparated).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_restrict_of_isIso_restrict_pullback_of_faithfullyFlat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.isIso_restrict_of_isIso_restrict_pullback_of_faithfullyFlat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L) (hM : Scheme.Modules.IsInvertible M)
    (θ : L ⟶ M) (W : X.Opens)
    (hθ : IsIso ((Scheme.Modules.pullback (c ⁻¹ᵁ W).ι).map ((Scheme.Modules.pullback c).map θ))) :
    IsIso ((Scheme.Modules.pullback W.ι).map θ) := by sorry
