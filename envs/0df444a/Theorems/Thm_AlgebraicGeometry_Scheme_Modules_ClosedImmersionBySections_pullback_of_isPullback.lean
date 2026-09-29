-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_of_isPullback
-- name    : AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.pullback_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/73eb5d85-3f17-51c8-b889-8c33afba4ce0
-- title:
--   Closed immersion by sections is stable under base change
-- statement:
--   Let $\varphi : R \to R'$ be a homomorphism of commutative rings, let $X, X'$ be schemes, let $f : X \to \operatorname{Spec} R$ and $f' : X' \to \operatorname{Spec} R'$ be morphisms, and let $g : X' \to X$ be such that the square formed by $g$, $f'$, $f$ and $\operatorname{Spec}(\varphi)$ is cartesian (i.e. `IsPullback g f' f (Spec.map (CommRingCat.ofHom φ))`: $g$ followed by $f$ equals $f'$ followed by $\operatorname{Spec}(\varphi)$, and the square is a limit). Let $M$ be an $\mathcal{O}_X$-module satisfying `ClosedImmersionBySections M f`, that is: there are an $N \in \mathbb{N}$ and a `ProjPresentation` of $M$ relative to $f$ of size $N$ — global sections $\sigma_0,\dots,\sigma_N \in \Gamma(M,\top)$ together with a morphism $\tau : X \to \operatorname{Proj}$ of the homogeneous subalgebra of $R[X_0,\dots,X_N]$ (that is, $\mathbb{P}^N_R$) whose composite with the projection to $\operatorname{Spec} R$ is $f$, such that for each $i$ and each open $V \subseteq \tau^{-1}(D(X_i))$ the map $\Gamma(X,V) \to \Gamma(M,V)$, $g \mapsto g \cdot \sigma_i|_V$, is bijective, and such that on $\tau^{-1}(D(X_i))$ the pullback along $\tau$ of the ratio $X_j/X_i$ acts on $\sigma_i$ to give $\sigma_j$ — and moreover $\tau$ is a closed immersion. The conclusion is that the pullback module $(\mathrm{pullback}\ g).obj\ M$ on $X'$ satisfies `ClosedImmersionBySections` relative to $f'$.
--
--   This is the base-change stability of the property that $N+1$ sections of $M$ present $X$ as a closed subscheme of $\mathbb{P}^N$ over the base, the sections-level form of "relatively very ample". It is used in the construction of level structures and polarised abelian scheme data, where ample packages produced over one base ring must be transported along ring maps.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_ClosedImmersionBySections_pullback_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections.pullback_of_isPullback
    {R R' : Type u} [CommRing R] [CommRing R'] (φ : R →+* R')
    {X X' : Scheme.{u}} {f : X ⟶ Spec (.of R)} {f' : X' ⟶ Spec (.of R')} (g : X' ⟶ X)
    (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
    {M : X.Modules} (hM : Scheme.Modules.ClosedImmersionBySections M f) :
    Scheme.Modules.ClosedImmersionBySections ((Scheme.Modules.pullback g).obj M) f' := by sorry
