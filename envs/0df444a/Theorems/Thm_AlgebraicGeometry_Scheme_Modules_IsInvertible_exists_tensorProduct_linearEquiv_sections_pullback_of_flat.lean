-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/9a18b2be-f8c7-5288-b18a-400f63eced79
-- title:
--   Flat base change for global sections of an invertible module
-- statement:
--   Let $S$ be a commutative ring and $S'$ a commutative $S$-algebra that is flat as an $S$-module. Let $X, X'$ be schemes, $f : X \to \operatorname{Spec} S$ a quasi-compact separated morphism, $f' : X' \to \operatorname{Spec} S'$ a morphism, and $c : X' \to X$ a morphism such that the square formed by $c$, $f'$, $f$ and $\operatorname{Spec}$ of the structure map $S \to S'$ is cartesian, as witnessed by `hc`. Let $M$ be a module over the structure sheaf of $X$ which is invertible in the sense that every point of $X$ has an open neighbourhood $U$ with the pullback of $M$ along the inclusion $U \hookrightarrow X$ isomorphic to the unit sheaf of modules on $U$. Equip $\Gamma(X, \top)$ with the $S$-algebra structure coming from the global sections map of $f$ (the inverse of the $\Gamma$–$\operatorname{Spec}$ isomorphism of $S$ followed by `f.appTop`), and $\Gamma(M, \top)$ with the resulting $S$-module structure by restriction of scalars along $S \to \Gamma(X,\top)$; likewise for $S'$, $\Gamma(X', \top)$ and the global sections of the pullback $c^{*}M$. The conclusion asserts the existence of an $S'$-linear equivalence $\beta : S' \otimes_S \Gamma(M, \top) \;\simeq\; \Gamma(c^{*}M, \top)$ satisfying $\beta(1 \otimes s) = s|_{X'}$ for every $s \in \Gamma(M, \top)$, where $s|_{X'}$ denotes the image of $s$ under the component at $\top$ of the unit of the pullback–pushforward adjunction along $c$ evaluated at $M$. Since the elements $1 \otimes s$ generate the source over $S'$, this pins $\beta$ down and says exactly that the canonical base-change map is bijective.
--
--   This is flat base change for the global sections of an invertible module over a quasi-compact separated base-affine scheme. It is used in the construction of the relative Picard functor and its rigidified line bundles, for instance in comparing polarisations and invertible modules after a flat or faithfully flat base change, and in the base-change property of section rings of graded algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.Flat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    letI : Algebra S Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra
    letI : Module S Γ(M, ⊤) := Module.compHom _ (algebraMap S Γ(X, ⊤))
    letI : Algebra S' Γ(X', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom.toAlgebra
    letI : Module S' Γ((Scheme.Modules.pullback c).obj M, ⊤) := Module.compHom _ (algebraMap S' Γ(X', ⊤))
    ∃ β : S' ⊗[S] Γ(M, ⊤) ≃ₗ[S'] Γ((Scheme.Modules.pullback c).obj M, ⊤),
      ∀ s : Γ(M, ⊤), β (1 ⊗ₜ s) = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app M).app ⊤) s := by sorry
