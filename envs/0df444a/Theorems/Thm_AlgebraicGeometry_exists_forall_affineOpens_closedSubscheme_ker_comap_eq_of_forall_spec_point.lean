-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point
-- name    : AlgebraicGeometry.exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/48959ee3-304d-50a3-8a9c-1ce9deefe506
-- title:
--   Affine-local models for a representing point datum
-- statement:
--   Let $S$ be a commutative ring, let $X$ and $H$ be schemes, and let $f : X \to \operatorname{Spec} S$ and $\pi_H : H \to \operatorname{Spec} S$ be morphisms. Suppose given a datum $\mathrm{pt}$ which, for every ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every closed immersion $\iota : Z \to X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ whose composite with the second projection is flat and locally of finite presentation, returns a morphism $\operatorname{Spec} S' \to H$ together with a proof that it is followed by $\pi_H$ gives $s$ (this is what `SchemeHomOver` records). Assume: (nat) for every ring map $\psi : S' \to S''$ with $\operatorname{Spec}\psi$ followed by $s$ equal to $s''$, and every pair of such data $(Z,\iota)$ over $s$ and $(Z'',\iota'')$ over $s''$ together with $e : Z'' \to Z$ making the square formed by $e$, the two structure morphisms and $\operatorname{Spec}\psi$ a pullback and satisfying $\iota''$ followed by the pullback map induced by $(\mathrm{id}_X, \operatorname{Spec}\psi)$ equals $e$ followed by $\iota$, the underlying morphism of $\mathrm{pt}(Z'')$ is $\operatorname{Spec}\psi$ followed by that of $\mathrm{pt}(Z)$; (surj) every element of `SchemeHomOver s πH` is $\mathrm{pt}$ of some such $(Z,\iota)$; (inj) two such data over the same $s$ with equal $\mathrm{pt}$ are related by an isomorphism $e : Z \cong Z'$ with $e$ followed by $\iota'$ equal to $\iota$. The conclusion asserts the existence of families indexed by the affine opens $V$ of $H$: schemes $Z_V$, closed immersions $\iota_V : Z_V \to X \times_{\operatorname{Spec} S} \operatorname{Spec}\Gamma(H,V)$ (the base change along $V$'s canonical morphism $\operatorname{Spec}\Gamma(H,V) \to H$ followed by $\pi_H$) whose composites with the second projection are flat and locally of finite presentation, and morphisms $j_V : Z_V \to p^{-1}(V)$, where $p$ is the projection $X \times_{\operatorname{Spec} S} H \to H$, such that: $\mathrm{pt}(Z_V, \iota_V)$ is the tautological point $\operatorname{Spec}\Gamma(H,V) \to H$ of $V$; each $j_V$ is a closed immersion; $j_V$ followed by the open immersion $p^{-1}(V) \to X \times_{\operatorname{Spec} S} H$ equals $\iota_V$ followed by the pullback map induced by $(\mathrm{id}_X, \operatorname{Spec}\Gamma(H,V) \to H)$; $j_V$ followed by the restriction of $p$ over $V$ is flat and locally of finite presentation; and for all affine opens $V, V'$ the ideal of $j_V$, pulled back along the inclusion $p^{-1}(V) \cap p^{-1}(V') \le p^{-1}(V)$, coincides with the ideal of $j_{V'}$ pulled back along $p^{-1}(V) \cap p^{-1}(V') \le p^{-1}(V')$.
--
--   This is the affine-local half of the construction of a universal flat, finitely presented closed subscheme of $X$ over a parameter scheme $H$ representing the point datum $\mathrm{pt}$, in the style of Hilbert-functor representability: over each affine open of $H$ the tautological point is realised by a concrete closed subscheme, and the resulting quasi-coherent ideals agree on overlaps. It is used by [`AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point`](thm.html#AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point), where these local ideals are glued into a single closed subscheme of $X \times_{\operatorname{Spec} S} H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem AlgebraicGeometry.exists_forall_affineOpens_closedSubscheme_ker_comap_eq_of_forall_spec_point
    (S : Type u) [CommRing S] {X H : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of S)) (πH : H ⟶ Spec (CommRingCat.of S))
    (pt : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{u}) (ι : Z ⟶ pullback f s), IsClosedImmersion ι → Flat (ι ≫ pullback.snd f s) →
          LocallyOfFinitePresentation (ι ≫ pullback.snd f s) → SchemeHomOver s πH)

    (hnat : ∀ (S' S'' : Type u) [CommRing S'] [CommRing S''] (ψ : S' →+* S'')
          (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (s'' : Spec (CommRingCat.of S'') ⟶ Spec (CommRingCat.of S))
          (hs : Spec.map (CommRingCat.ofHom ψ) ≫ s = s'')
          (Z : Scheme.{u}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s))
          (Z'' : Scheme.{u}) (ι'' : Z'' ⟶ pullback f s'') (hι'' : IsClosedImmersion ι'') (hfl'' : Flat (ι'' ≫ pullback.snd f s''))
          (hfp'' : LocallyOfFinitePresentation (ι'' ≫ pullback.snd f s''))
          (e : Z'' ⟶ Z),
          IsPullback e (ι'' ≫ pullback.snd f s'') (ι ≫ pullback.snd f s) (Spec.map (CommRingCat.ofHom ψ)) →
          ι'' ≫ pullback.map f s'' f s (𝟙 X) (Spec.map (CommRingCat.ofHom ψ)) (𝟙 _)
              (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.comp_id, hs]) = e ≫ ι →
          (pt S'' s'' Z'' ι'' hι'' hfl'' hfp'').1 = Spec.map (CommRingCat.ofHom ψ) ≫ (pt S' s Z ι hι hfl hfp).1)

    (hsurj : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver s πH),
        ∃ (Z : Scheme.{u}) (ι : Z ⟶ pullback f s) (hι : IsClosedImmersion ι) (hfl : Flat (ι ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)),
          pt S' s Z ι hι hfl hfp = x)

    (hinj : ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
          (Z Z' : Scheme.{u}) (ι : Z ⟶ pullback f s) (ι' : Z' ⟶ pullback f s)
          (hι : IsClosedImmersion ι) (hι' : IsClosedImmersion ι')
          (hfl : Flat (ι ≫ pullback.snd f s)) (hfl' : Flat (ι' ≫ pullback.snd f s))
          (hfp : LocallyOfFinitePresentation (ι ≫ pullback.snd f s)) (hfp' : LocallyOfFinitePresentation (ι' ≫ pullback.snd f s)),
        pt S' s Z ι hι hfl hfp = pt S' s Z' ι' hι' hfl' hfp' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι) :
    ∃ (ZV : H.affineOpens → Scheme.{u})
      (ιV : ∀ V : H.affineOpens, ZV V ⟶ pullback f (V.2.fromSpec ≫ πH))
      (hclV : ∀ V : H.affineOpens, IsClosedImmersion (ιV V))
      (hflV : ∀ V : H.affineOpens, Flat (ιV V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
      (hfpV : ∀ V : H.affineOpens, LocallyOfFinitePresentation (ιV V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
      (jV : ∀ V : H.affineOpens, ZV V ⟶ ↑((pullback.snd f πH) ⁻¹ᵁ V.1)),
      (∀ V : H.affineOpens,
        pt Γ(H, V.1) (V.2.fromSpec ≫ πH) (ZV V) (ιV V) (hclV V) (hflV V) (hfpV V) = ⟨V.2.fromSpec, rfl⟩) ∧
      (∀ V : H.affineOpens, IsClosedImmersion (jV V)) ∧
      (∀ V : H.affineOpens,
        jV V ≫ ((pullback.snd f πH) ⁻¹ᵁ V.1).ι =
          ιV V ≫ pullback.map f (V.2.fromSpec ≫ πH) f πH (𝟙 X) V.2.fromSpec (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id])) ∧
      (∀ V : H.affineOpens, Flat (jV V ≫ (pullback.snd f πH) ∣_ V.1)) ∧
      (∀ V : H.affineOpens, LocallyOfFinitePresentation (jV V ≫ (pullback.snd f πH) ∣_ V.1)) ∧
      (∀ V V' : H.affineOpens,
        (jV V).ker.comap ((pullback f πH).homOfLE
            (inf_le_left : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V.1)) =
        (jV V').ker.comap ((pullback f πH).homOfLE
            (inf_le_right : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V'.1))) := by sorry
