-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point
-- name    : AlgebraicGeometry.exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/a7ae0d5f-021a-5974-be90-f06aec707785
-- title:
--   Universal morphism glued from affine points of M
-- statement:
--   Let $S$ be a commutative ring, let $X$, $Y$, $M$ be schemes and let $f : X \to \operatorname{Spec} S$, $g : Y \to \operatorname{Spec} S$, $\pi_M : M \to \operatorname{Spec} S$ be morphisms. Suppose given data `pt` attaching, to every commutative ring $S'$, every morphism $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every $\varphi : X \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to Y$ satisfying $\varphi \mathbin{;} g = \mathrm{pr}_2 \mathbin{;} s$, a pair consisting of a morphism $\mathrm{pt}(\varphi) : \operatorname{Spec} S' \to M$ together with a proof that $\mathrm{pt}(\varphi) \mathbin{;} \pi_M = s$. Assume three conditions: naturality, namely for every ring homomorphism $\psi : S' \to S''$ and every $s, s''$ with $\operatorname{Spec}(\psi) \mathbin{;} s = s''$, the point attached to the pullback of $\varphi$ along the canonical map $X \times_S \operatorname{Spec} S'' \to X \times_S \operatorname{Spec} S'$ (induced by $\mathrm{id}_X$ and $\operatorname{Spec}(\psi)$) equals $\operatorname{Spec}(\psi)$ followed by $\mathrm{pt}(\varphi)$; surjectivity, namely every morphism $\operatorname{Spec} S' \to M$ over $s$ is $\mathrm{pt}(\varphi)$ for some admissible $\varphi$; and injectivity, namely $\mathrm{pt}(\varphi) = \mathrm{pt}(\varphi')$ forces $\varphi = \varphi'$. Then there is a morphism $\Phi : X \times_{\operatorname{Spec} S} M \to Y$ with $\Phi \mathbin{;} g = \mathrm{pr}_2 \mathbin{;} \pi_M$ such that for all $S'$, $s$ and admissible $\varphi$, the base-change morphism $X \times_S \operatorname{Spec} S' \to X \times_S M$ determined by $\mathrm{id}_X$ and $\mathrm{pt}(\varphi)$, followed by $\Phi$, equals $\varphi$.
--
--   This is the passage from a functor of morphisms represented on affine points to the universal family over the representing scheme: the hypotheses express that $M$, as a scheme over $\operatorname{Spec} S$, represents $S' \mapsto \{\varphi : X \times_S \operatorname{Spec} S' \to Y \text{ over } S'\}$ on affine $S$-schemes, and the conclusion produces the tautological morphism over $M$ pulling back to each $\varphi$. It is used in the construction of the scheme of homomorphisms in the relative group law package, where the Hom-scheme is cut out of a Mor-scheme and the universal family over the (in general non-affine) representing scheme is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem AlgebraicGeometry.exists_hom_pullback_comp_eq_and_forall_pullbackMap_comp_eq_of_forall_spec_point
    (S : Type u) [CommRing S] {X Y M : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (g : Y ⟶ Spec (CommRingCat.of S)) (πM : M ⟶ Spec (CommRingCat.of S))
    (pt : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : pullback f s ⟶ Y), φ ≫ g = pullback.snd f s ≫ s → SchemeHomOver s πM)

    (hnat : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        (pt S'' s''
            (pullback.lift (pullback.fst f s'') (pullback.snd f s'' ≫ Spec.map (CommRingCat.ofHom ψ))
                (by rw [Category.assoc, hs]; exact pullback.condition) ≫ φ)
            (by rw [Category.assoc, hφ, ← Category.assoc, pullback.lift_snd, Category.assoc, hs])).1 =
          Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s φ hφ).1)

    (hsurj : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πM),
        ∃ (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s), pt S' s φ hφ = x)

    (hinj : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (φ φ' : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s) (hφ' : φ' ≫ g = pullback.snd f s ≫ s),
        pt S' s φ hφ = pt S' s φ' hφ' → φ = φ') :
    ∃ Φ : pullback f πM ⟶ Y, Φ ≫ g = pullback.snd f πM ≫ πM ∧
      ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (φ : pullback f s ⟶ Y) (hφ : φ ≫ g = pullback.snd f s ≫ s),
        pullback.map f s f πM (𝟙 X) (pt S' s φ hφ).1 (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s φ hφ).2]) ≫ Φ = φ := by sorry
