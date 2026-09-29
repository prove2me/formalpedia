-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_iso_over_of_forall_schemeHomOver_equiv
-- name    : AlgebraicGeometry.Scheme.exists_iso_over_of_forall_schemeHomOver_equiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/f16798b5-ef97-527a-a2ba-1892bd9e7ab2
-- title:
--   Schemes over an affine base are determined by affine points
-- statement:
--   Let $R$ be a commutative ring and let $\zeta_1 : Z_1 \to \operatorname{Spec} R$, $\zeta_2 : Z_2 \to \operatorname{Spec} R$ be morphisms of schemes. For a commutative ring $T$ and a ring homomorphism $\varphi : R \to T$, write $Z_i(T)_\varphi$ for the set of pairs consisting of a morphism $u : \operatorname{Spec} T \to Z_i$ together with a proof that $u$ followed by $\zeta_i$ equals $\operatorname{Spec}\varphi$. Assume given, for every such $(T,\varphi)$, a bijection $e_{T,\varphi} : Z_1(T)_\varphi \to Z_2(T)_\varphi$, and assume these bijections are natural in the test ring: for all ring homomorphisms $\varphi : R \to T$ and $\psi : T \to T'$ and every $x \in Z_1(T)_\varphi$, the underlying morphism of $e_{T',\psi\circ\varphi}$ applied to $\operatorname{Spec}\psi$ followed by $x$ equals $\operatorname{Spec}\psi$ followed by the underlying morphism of $e_{T,\varphi}(x)$. The conclusion asserts the existence of an isomorphism $\varepsilon : Z_1 \cong Z_2$ such that $\varepsilon$ followed by $\zeta_2$ equals $\zeta_1$, such that for all $(T,\varphi)$ and all $x \in Z_1(T)_\varphi$ one has $x$ followed by $\varepsilon$ equal to the underlying morphism of $e_{T,\varphi}(x)$, and such that $\varepsilon$ is the unique morphism $Z_1 \to Z_2$ with this last property.
--
--   This is the rigidity statement that a scheme over an affine base is determined, up to a unique isomorphism over the base, by its functor of points restricted to affine test schemes: a bijection of affine-point sets natural in the test ring is induced by a unique isomorphism. It is used in the Čerednik–Drinfeld material, in [`CerednikDrinfeld.QM.exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying`](thm.html#CerednikDrinfeld.QM.exists_transition_isPullback_of_represents_qmStructure_affineOpens_satisfying), to transfer an identification of moduli functors on affine charts into an isomorphism of the representing schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_exists_iso_over_of_forall_schemeHomOver_equiv.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

universe u

theorem AlgebraicGeometry.Scheme.exists_iso_over_of_forall_schemeHomOver_equiv
    {R : Type u} [CommRing R] {Z₁ Z₂ : Scheme.{u}}
    (ζ₁ : Z₁ ⟶ Spec (CommRingCat.of R)) (ζ₂ : Z₂ ⟶ Spec (CommRingCat.of R))
    (e : ∀ (T : Type u) [CommRing T] (φ : R →+* T),
      SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁ ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₂)
    (he : ∀ (T T' : Type u) [CommRing T] [CommRing T'] (φ : R →+* T) (ψ : T →+* T')
      (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
      (e T' (ψ.comp φ) ⟨Spec.map (CommRingCat.ofHom ψ) ≫ x.1, by
          rw [Category.assoc, x.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩).1 =
        Spec.map (CommRingCat.ofHom ψ) ≫ (e T φ x).1) :
    ∃ ε : Z₁ ≅ Z₂, ε.hom ≫ ζ₂ = ζ₁ ∧
      (∀ (T : Type u) [CommRing T] (φ : R →+* T) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
        x.1 ≫ ε.hom = (e T φ x).1) ∧
      ∀ ε' : Z₁ ⟶ Z₂, (∀ (T : Type u) [CommRing T] (φ : R →+* T) (x : SchemeHomOver (Spec.map (CommRingCat.ofHom φ)) ζ₁),
        x.1 ≫ ε' = (e T φ x).1) → ε' = ε.hom := by sorry
