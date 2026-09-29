-- Prove2me | Theorems.Thm_AlgebraicGeometry_isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen
-- name    : AlgebraicGeometry.isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.489634+00:00
-- url     : https://prove2.me/theorems/68dcdb94-ec86-5851-af75-7535479b00ac
-- title:
--   Sections over p⁻¹V localise the sections over an affine open
-- statement:
--   Let $R$ be a commutative ring, $M \subseteq R$ a submonoid, and let $T$ be an $R$-algebra that is a localisation of $R$ at $M$. Let $B$ be a scheme, $q : B \to \operatorname{Spec} R$ a morphism, and $V$ an open subset of $B$ which is an affine open. Write $\iota = \operatorname{Spec}$ of the structure map $R \to T$ and $p =$ `pullback.fst` $: B \times_{\operatorname{Spec} R} \operatorname{Spec} T \to B$. Equip $\Gamma(B \times_{\operatorname{Spec} R} \operatorname{Spec} T,\ p^{-1}V)$ with the $\Gamma(B,V)$-algebra structure coming from the ring map $p^{\sharp}_V$, the component at $V$ of the morphism $p$ on sections. The assertion is that this algebra is a localisation of $\Gamma(B,V)$ at the image of $M$ under the multiplicative map $R \to \Gamma(B,V)$ obtained by composing the inverse of the canonical isomorphism $\Gamma(\operatorname{Spec} R, \top) \cong R$, the map $q^{\sharp}_{\top}$ on global sections, and the restriction $\Gamma(B,\top) \to \Gamma(B,V)$; that is, `IsLocalization` holds for this submonoid of $\Gamma(B,V)$ and this algebra.
--
--   This is the statement that base change of a scheme along a localisation $R \to T$ localises the sections over each affine open, in the form of an `IsLocalization` instance. It is used in the study of invertible modules and descent of isomorphisms on schemes, where local data at a prime must be spread out over a localisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen
    {R : Type u} [CommRing R] (M : Submonoid R) (T : Type u) [CommRing T] [Algebra R T] [IsLocalization M T]
    {B : Scheme.{u}} (q : B ⟶ Spec (CommRingCat.of R)) (V : B.Opens) (hV : IsAffineOpen V) :
    letI := ((pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R T)))).app V).hom.toAlgebra
    IsLocalization
      (M.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appTop ≫
          B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom : R →* Γ(B, V)))
      Γ(pullback q (Spec.map (CommRingCat.ofHom (algebraMap R T))),
        pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R T))) ⁻¹ᵁ V) := by sorry
