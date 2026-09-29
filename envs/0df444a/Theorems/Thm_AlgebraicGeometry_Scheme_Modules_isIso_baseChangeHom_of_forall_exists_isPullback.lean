-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback
-- name    : AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_forall_exists_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/d8664c40-c912-5014-8f51-2829258c03b3
-- title:
--   Base change for direct images is local on the base
-- statement:
--   Let $X, T, X', T'$ be schemes and let $\pi : X \to T$, $\psi : T' \to T$, $\pi' : X' \to T'$, $g' : X' \to X$ be morphisms such that `hcart` exhibits the square with $g', \pi'$ over $\pi, \psi$ as a pullback, and let $F$ be a sheaf of modules on $X$. Assume that for every point $y$ of $T'$ there are an open $W \subseteq T$, an open $W' \subseteq T'$ with $y \in W'$, schemes $S, S', Y, Y'$, isomorphisms $e : S \cong W$ and $e' : S' \cong W'$, and a morphism $\varphi : S' \to S$ such that $e'$ followed by the inclusion $W' \hookrightarrow T'$ followed by $\psi$ equals $\varphi$ followed by $e$ followed by the inclusion $W \hookrightarrow T$; further, morphisms $\rho : Y \to S$ and $u : Y \to X$ making the square with $u, \rho$ over $\pi$ and $S \to W \hookrightarrow T$ a pullback, and morphisms $\rho' : Y' \to S'$ and $v : Y' \to Y$ making the square `hv` with $v, \rho'$ over $\rho, \varphi$ a pullback, for which the base-change morphism $\varphi^{*}\rho_{*}(u^{*}F) \to \rho'_{*}v^{*}(u^{*}F)$ attached to the commuting square underlying `hv` is an isomorphism. Then the base-change morphism $\psi^{*}\pi_{*}F \to \pi'_{*}g'^{*}F$ attached to the commuting square underlying `hcart` is an isomorphism. Here the base-change morphism of a commuting square $g' \circ \pi = \psi \circ \pi'$ is the component at $F$ of the mate, with respect to the pullback–pushforward adjunctions for $\psi$ and for $\pi'$, of the two-square comparing pullbacks along the square.
--
--   This is the statement that formation of direct images of sheaves of modules commutes with base change is a property local on the base, and insensitive to replacing the base opens by isomorphic models (for instance affine ones): the degree-zero case of cohomology and base change, in the reduction-to-the-affine-case form. It is the reduction step used by the relative Picard constructions, namely [`AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre`](thm.html#AlgebraicGeometry.RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre) and its variants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_forall_exists_isPullback.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Modules.isIso_baseChangeHom_of_forall_exists_isPullback
    {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    (hcart : IsPullback g' π' π ψ) (F : X.Modules)
    (h : ∀ y : T', ∃ (W : T.Opens) (W' : T'.Opens) (_ : y ∈ W') (S S' Y Y' : Scheme.{u})
      (e : S ≅ W.toScheme) (e' : S' ≅ W'.toScheme) (φ : S' ⟶ S)
      (_ : (e'.hom ≫ W'.ι) ≫ ψ = φ ≫ e.hom ≫ W.ι)
      (ρ : Y ⟶ S) (u : Y ⟶ X) (_ : IsPullback u ρ π (e.hom ≫ W.ι))
      (ρ' : Y' ⟶ S') (v : Y' ⟶ Y) (hv : IsPullback v ρ' ρ φ),
      IsIso (Scheme.Modules.baseChangeHom hv.w ((Scheme.Modules.pullback u).obj F))) :
    IsIso (Scheme.Modules.baseChangeHom hcart.w F) := by sorry
