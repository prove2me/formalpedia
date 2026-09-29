-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_existsUnique_ringHom_stalk_comp_eq_and_specMap_comp_fromSpecStalk_eq
-- name    : AlgebraicGeometry.Scheme.existsUnique_ringHom_stalk_comp_eq_and_specMap_comp_fromSpecStalk_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/070ab816-f05f-514c-926f-5aad86a09e66
-- title:
--   A-valued points of X centred at a K-point ̄ x
-- statement:
--   Let $X$ be a scheme, $x$ a point of $X$, and $K$ a field equipped with a ring homomorphism $\bar x \colon \mathcal O_{X,x} \to K$ from the stalk of the structure sheaf at $x$ whose kernel is exactly the maximal ideal of that local ring. Let $A$ be a local commutative ring together with a surjective ring homomorphism $\mathrm{res}_A \colon A \to K$. Two assertions are made. First, for every ring homomorphism $\psi \colon \mathcal O_{X,x} \to A$ with $\mathrm{res}_A \circ \psi = \bar x$, the composite $\operatorname{Spec} K \to \operatorname{Spec} A \to \operatorname{Spec} \mathcal O_{X,x} \to X$, formed from $\operatorname{Spec}(\mathrm{res}_A)$, $\operatorname{Spec}(\psi)$ and the canonical morphism `X.fromSpecStalk x`, equals the composite of $\operatorname{Spec}(\bar x)$ with `X.fromSpecStalk x`; in other words $g_\psi := \operatorname{Spec}(\psi)$ followed by `X.fromSpecStalk x` is centred at $\bar x$. Second, conversely, for every morphism of schemes $g \colon \operatorname{Spec} A \to X$ such that $\operatorname{Spec}(\mathrm{res}_A)$ followed by $g$ equals $\operatorname{Spec}(\bar x)$ followed by `X.fromSpecStalk x`, there is a unique ring homomorphism $\psi \colon \mathcal O_{X,x} \to A$ satisfying both $\mathrm{res}_A \circ \psi = \bar x$ and $g_\psi = g$.
--
--   This is the description of morphisms from the spectrum of a local ring into a scheme (EGA I, 2.4.4), specialised to those $A$-valued points whose closed point lands at $x$ with prescribed residue homomorphism $\bar x$: such points correspond bijectively to the residue-compatible homomorphisms $\mathcal O_{X,x} \to A$. It is used in the study of fine moduli schemes for quaternionic data, where points of the moduli scheme with values in local (in practice, artinian or complete local) rings are matched with the deformations classified by the corresponding deformation functor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_existsUnique_ringHom_stalk_comp_eq_and_specMap_comp_fromSpecStalk_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry in

theorem AlgebraicGeometry.Scheme.existsUnique_ringHom_stalk_comp_eq_and_specMap_comp_fromSpecStalk_eq
    (X : Scheme.{u}) (x : X) (K : Type u) [Field K]
    (xbar : X.presheaf.stalk x →+* K)
    (hxbar : RingHom.ker xbar = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (A : Type u) [CommRing A] [IsLocalRing A] (resA : A →+* K) (hresA : Function.Surjective resA) :
    (∀ ψ : X.presheaf.stalk x →+* A, resA.comp ψ = xbar →
        Spec.map (CommRingCat.ofHom resA) ≫ (Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x) =
          Spec.map (CommRingCat.ofHom xbar) ≫ X.fromSpecStalk x) ∧
    (∀ g : Spec (CommRingCat.of A) ⟶ X,
        Spec.map (CommRingCat.ofHom resA) ≫ g = Spec.map (CommRingCat.ofHom xbar) ≫ X.fromSpecStalk x →
        ∃! ψ : X.presheaf.stalk x →+* A, resA.comp ψ = xbar ∧
          Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x = g) := by sorry
