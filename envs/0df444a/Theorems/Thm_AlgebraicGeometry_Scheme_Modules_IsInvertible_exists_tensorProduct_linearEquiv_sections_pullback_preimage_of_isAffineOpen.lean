-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/a6907bba-a2e6-556e-a63f-3dacebc5f00f
-- title:
--   Affine base change of sections of an invertible module
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra, and let $f : X \to \operatorname{Spec} S$ and $f' : X' \to \operatorname{Spec} S'$ be morphisms of schemes together with $c : X' \to X$ such that the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ is cartesian (hypothesis `hc`). Let $M$ be an object of `X.Modules` which is invertible in the sense of `Scheme.Modules.IsInvertible`, i.e. every point of $X$ has an open neighbourhood $V$ such that the pullback of $M$ along the inclusion $V \hookrightarrow X$ is isomorphic to the unit sheaf of modules on $V$, and let $U$ be an open subset of $X$ which is affine. Equip $\Gamma(X,U)$ with the $S$-algebra structure coming from $f$ on global sections restricted to $U$ (via the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism for $S$) and $\Gamma(M,U)$ with the resulting $S$-module structure, and likewise $\Gamma(X', c^{-1}U)$ with the $S'$-algebra structure coming from $f'$ and $\Gamma(c^{*}M, c^{-1}U)$ with the resulting $S'$-module structure. Then there exists an $S'$-linear isomorphism $\beta : S' \otimes_S \Gamma(M,U) \to \Gamma(c^{*}M, c^{-1}U)$ such that $\beta(1 \otimes s)$ is, for every $s \in \Gamma(M,U)$, the value at $s$ of the component at $U$ of the unit of the pullback–pushforward adjunction along $c$ evaluated at $M$.
--
--   This is affine base change for the sections of an invertible module, in the pinned form which records that the comparison map sends $1 \otimes s$ to the canonical image $c^{*}s$; no flatness of $S \to S'$ is required. It feeds the passage to non-affine bases in [`AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat`](thm.html#AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat) and the computation of the unit map on adic thickenings used in the relative Picard functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (U : X.Opens) (hU : IsAffineOpen U) :
    letI : Algebra S Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ U le_top).hom.toAlgebra
    letI : Module S Γ(M, U) := Module.compHom _ (algebraMap S Γ(X, U))
    letI : Algebra S' Γ(X', c ⁻¹ᵁ U) :=
      ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (c ⁻¹ᵁ U) le_top).hom.toAlgebra
    letI : Module S' Γ((Scheme.Modules.pullback c).obj M, c ⁻¹ᵁ U) :=
      Module.compHom _ (algebraMap S' Γ(X', c ⁻¹ᵁ U))
    ∃ β : S' ⊗[S] Γ(M, U) ≃ₗ[S'] Γ((Scheme.Modules.pullback c).obj M, c ⁻¹ᵁ U),
      ∀ s : Γ(M, U), β (1 ⊗ₜ s) = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M).app U) s := by sorry
