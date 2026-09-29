-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_closedImmersionBySections_of_faithfullyFlat_of_isPullback
-- name    : AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_faithfullyFlat_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.777313+00:00
-- url     : https://prove2.me/theorems/41ed6795-3a5c-59eb-95fc-f06a51738af7
-- title:
--   Closed immersion by sections descends along faithfully flat base change
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra which is faithfully flat as an $S$-module. Let $X$, $X'$ be schemes and $f : X \to \operatorname{Spec} S$, $f' : X' \to \operatorname{Spec} S'$, $c : X' \to X$ morphisms such that the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ is a pullback. Let $L$ be a sheaf of modules on $X$ which is invertible in the sense of `Scheme.Modules.IsInvertible`, i.e. every point of $X$ has an open neighbourhood $U$ such that the pullback of $L$ along the inclusion $U \hookrightarrow X$ is isomorphic to the unit module on $U$; let $L'$ be a sheaf of modules on $X'$ admitting an isomorphism $c^{*}L \cong L'$ (the hypothesis is the nonemptiness of the type of such isomorphisms). Assume `ClosedImmersionBySections L' f'`: there are $M \in \mathbb{N}$ and a `ProjPresentation` of $L'$ over $f'$ of size $M$ — that is, sections $\sigma_0,\dots,\sigma_M \in \Gamma(L', \top)$ together with a morphism $X' \to \mathbb{P}^M_{S'}$ (the $\operatorname{Proj}$ of the homogeneous subalgebra of $S'[X_0,\dots,X_M]$) whose composite with the structure morphism $\pi$ is $f'$, such that over any open $V$ contained in the preimage of the standard basic open $D(X_i)$ multiplication by the restriction of $\sigma_i$ is a bijection $\Gamma(X',V) \to \Gamma(L',V)$, and such that the pullback of the ratio $X_j/X_i$ scales $\sigma_i$ into $\sigma_j$ over the preimage of $D(X_i)$ — whose structural morphism $X' \to \mathbb{P}^M_{S'}$ is a closed immersion. The conclusion is `ClosedImmersionBySections L f`: for some $N$ there is such a presentation of $L$ over $f$ by $N+1$ global sections whose associated morphism $X \to \mathbb{P}^N_S$ is a closed immersion.
--
--   This is the descent, along a faithfully flat base change $S \to S'$, of the property that an invertible module is very ample relative to the base in the explicit form of a presentation of $X$ as a closed subscheme of a projective space by global sections. It is used in the descent statement [`AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_closedImmersionBySections_of_rigidified`](thm.html#AlgebraicGeometry.exists_descent_of_faithfullyFlat_of_closedImmersionBySections_of_rigidified), which underlies the construction of relative Picard data by descent.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_closedImmersionBySections_of_faithfullyFlat_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.closedImmersionBySections_of_faithfullyFlat_of_isPullback
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (L' : X'.Modules)
    (hcL : Nonempty ((Scheme.Modules.pullback c).obj L ≅ L'))
    (hva : Scheme.Modules.ClosedImmersionBySections L' f') :
    Scheme.Modules.ClosedImmersionBySections L f := by sorry
