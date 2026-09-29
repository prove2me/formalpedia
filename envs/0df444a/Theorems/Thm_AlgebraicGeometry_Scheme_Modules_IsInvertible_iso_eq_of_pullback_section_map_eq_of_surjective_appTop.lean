-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_iso_eq_of_pullback_section_map_eq_of_surjective_appTop
-- name    : AlgebraicGeometry.Scheme.Modules.IsInvertible.iso_eq_of_pullback_section_map_eq_of_surjective_appTop
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:47.517283+00:00
-- url     : https://prove2.me/theorems/996f6416-a777-5c21-91c2-fe324bc74ffe
-- title:
--   Isomorphisms of an invertible module agreeing along a section
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme, and $f : A \to \operatorname{Spec} S$ a morphism admitting a section $e : \operatorname{Spec} S \to A$, meaning $e$ followed by $f$ is the identity of $\operatorname{Spec} S$. Assume the ring map induced by $f$ on global sections, $f^{\sharp} : \Gamma(\operatorname{Spec} S, \mathcal{O}) \to \Gamma(A, \mathcal{O}_A)$, is surjective. Let $L$ and $M$ be sheaves of modules on $A$, and suppose $L$ satisfies `Scheme.Modules.IsInvertible`: every point of $A$ has an open neighbourhood $U$ such that the restriction of $L$ along the inclusion $U \hookrightarrow A$ is isomorphic to the unit module of the sheaf of rings of $U$. Let $\alpha, \beta : L \cong M$ be two isomorphisms of modules on $A$, and assume that the pullback functor along $e$ carries the underlying morphism of $\alpha$ and the underlying morphism of $\beta$ to the same morphism $e^{*}L \to e^{*}M$. Then $\alpha = \beta$ as isomorphisms.
--
--   This is the statement that a line bundle rigidified along a section has no non-trivial automorphisms, in the form asserting uniqueness of an isomorphism with prescribed restriction along the section, under the hypothesis that all global functions on $A$ come from the base. It is used in the construction of the relative Picard functor and of rigidified line bundles: the existence-and-uniqueness statement for isomorphisms matching a given trivialisation, the cocycle identity for pullbacks of such isomorphisms, and the compatibility of composition with pullback along $e$ all cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_iso_eq_of_pullback_section_map_eq_of_surjective_appTop.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.iso_eq_of_pullback_section_map_eq_of_surjective_appTop
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    (e : Spec (CommRingCat.of S) ⟶ A) (he : e ≫ f = 𝟙 _)
    (hΓ : Function.Surjective (f.appTop).hom)
    (L M : A.Modules) (hL : Scheme.Modules.IsInvertible L)
    (α β : L ≅ M)
    (h : (Scheme.Modules.pullback e).map α.hom = (Scheme.Modules.pullback e).map β.hom) :
    α = β := by sorry
