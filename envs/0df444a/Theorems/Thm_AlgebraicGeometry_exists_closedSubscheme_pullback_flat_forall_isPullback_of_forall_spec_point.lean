-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point
-- name    : AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/012d59a7-4c4b-5336-9dbc-9cd2cac5fed2
-- title:
--   Universal flat closed subscheme from affine-point data
-- statement:
--   Let $S$ be a commutative ring, let $X$ and $H$ be schemes, and let $f : X \to \operatorname{Spec} S$ and $\pi_H : H \to \operatorname{Spec} S$ be morphisms. Suppose given an assignment `pt` which, for every commutative ring $S'$, every morphism $s : \operatorname{Spec} S' \to \operatorname{Spec} S$, and every closed immersion $\iota : Z \to X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ whose composite with the second projection makes $Z$ flat and locally of finite presentation over $\operatorname{Spec} S'$, produces an element of `SchemeHomOver s πH`, that is a pair consisting of a morphism $\varphi : \operatorname{Spec} S' \to H$ together with a proof that $\varphi \circ \pi_H = s$. Assume three conditions on `pt`: (hnat) naturality, namely that for a ring map $\psi : S' \to S''$ with $\operatorname{Spec}\psi \circ s = s''$, and data $Z, \iota$ over $s$ and $Z'', \iota''$ over $s''$ together with $e : Z'' \to Z$ exhibiting $Z''$ as the pullback of $Z$ along $\operatorname{Spec}\psi$ and compatible with the two closed immersions over $X$, one has $\mathrm{pt}(Z'') = \operatorname{Spec}\psi \circ \mathrm{pt}(Z)$; (hsurj) every element of `SchemeHomOver s πH` is $\mathrm{pt}$ of some such $Z, \iota$; (hinj) if two such subschemes over the same $s$ have the same image under `pt`, they are isomorphic over $X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$. The conclusion asserts the existence of a scheme $\mathcal{Z}$ and a closed immersion $\iota : \mathcal{Z} \to X \times_{\operatorname{Spec} S} H$ with $\mathcal{Z}$ flat and locally of finite presentation over $H$, such that for every $S'$, every $s$, and every closed immersion $\iota_Z : Z \to X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ flat and locally of finite presentation over $\operatorname{Spec} S'$, there is a morphism $e : Z \to \mathcal{Z}$ making the square formed by $e$, the two structure morphisms and $\mathrm{pt}(Z)$ a pullback, and satisfying the compatibility $\iota_Z$ followed by the map $X \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to X \times_{\operatorname{Spec} S} H$ induced by $\mathrm{pt}(Z)$ equals $e$ followed by $\iota$.
--
--   This is the passage from a functor of points described only on affine bases to a universal object: given that $H$ corepresents, on affine $S$-schemes, the functor of closed subschemes of $X$ that are flat and locally of finite presentation over the base, it produces the universal such subscheme $\mathcal{Z} \subseteq X \times_{\operatorname{Spec} S} H$ over the possibly non-affine $H$, in the style of the classical construction of the Hilbert scheme and its universal family. It is used in the project's representability statement for the functor of morphisms built from Hilbert pieces, whose consumers need a family over the base $H$ rather than pointwise data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point
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
    ∃ (𝒵 : Scheme.{u}) (ι : 𝒵 ⟶ pullback f πH), IsClosedImmersion ι ∧ Flat (ι ≫ pullback.snd f πH) ∧
      LocallyOfFinitePresentation (ι ≫ pullback.snd f πH) ∧
      ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{u}) (ιZ : Z ⟶ pullback f s) (hι : IsClosedImmersion ιZ) (hfl : Flat (ιZ ≫ pullback.snd f s))
        (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd f s)),
        ∃ e : Z ⟶ 𝒵,
          IsPullback e (ιZ ≫ pullback.snd f s) (ι ≫ pullback.snd f πH) (pt S' s Z ιZ hι hfl hfp).1 ∧
          ιZ ≫ pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _)
              (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2]) = e ≫ ι := by sorry
