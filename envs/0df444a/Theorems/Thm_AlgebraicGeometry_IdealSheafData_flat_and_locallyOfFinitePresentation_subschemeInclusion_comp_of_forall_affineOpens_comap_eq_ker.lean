-- Prove2me | Theorems.Thm_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker
-- name    : AlgebraicGeometry.IdealSheafData.flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/380d545c-90c6-5326-8b89-4b495db59cb5
-- title:
--   Flatness and finite presentation of the glued closed subscheme
-- statement:
--   Let $S$ be a commutative ring, let $X$ and $H$ be schemes, and let $f : X \to \operatorname{Spec} S$ and $\pi_H : H \to \operatorname{Spec} S$ be morphisms. Assume given a family of data: an assignment `pt` which, for every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every closed immersion $\iota : Z \to X \times_{\operatorname{Spec} S, s} \operatorname{Spec} S'$ whose composite with the second projection is flat and locally of finite presentation, produces an element of `SchemeHomOver s πH`, i.e. a morphism $\operatorname{Spec} S' \to H$ whose composite with $\pi_H$ is $s$; hypotheses `hnat`, `hsurj`, `hinj` asserting that `pt` is compatible with base change along ring homomorphisms, surjective and injective up to isomorphism of the closed subschemes; schemes $Z_V$ for each affine open $V \subseteq H$ together with closed immersions $\iota_V : Z_V \to X \times_{\operatorname{Spec} S} \operatorname{Spec} \Gamma(H,V)$ flat and locally of finite presentation over $\operatorname{Spec}\Gamma(H,V)$, satisfying the tautology `htaut` that `pt` sends them to the canonical morphism $\operatorname{Spec}\Gamma(H,V) \to H$; morphisms $j_V : Z_V \to p^{-1}(V)$, where $p = \mathrm{pr}_2 : X \times_{\operatorname{Spec} S} H \to H$, which are closed immersions (`hjcl`), are compatible with $\iota_V$ under the canonical map $p^{-1}(V) \to X \times_{\operatorname{Spec} S}\operatorname{Spec}\Gamma(H,V)$ (`hjV`), are flat (`hjfl`) and locally of finite presentation (`hjfp`) over $V$ after composing with the restriction $p|_V$, and whose kernels agree on overlaps $p^{-1}(V) \cap p^{-1}(V')$ (`hcompat`); and finally an ideal sheaf datum $I_0$ on $X \times_{\operatorname{Spec} S} H$ whose pullback along the open immersion $p^{-1}(V) \hookrightarrow X \times_{\operatorname{Spec} S} H$ equals $\ker(j_V)$ for every affine open $V$. The conclusion is that the closed immersion $I_0.\mathrm{subschemeι}$ followed by $p$ is flat and locally of finite presentation.
--
--   This is the descent step which upgrades local flatness and local finite presentation of the candidate closed subschemes $Z_V$ over a cover of $H$ by affine opens to the corresponding global properties of the closed subscheme cut out by the glued ideal sheaf. It is carried with the full binder list of the universal-property statement it serves, [`AlgebraicGeometry.exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq`](thm.html#AlgebraicGeometry.exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq), so that it can be applied there directly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IdealSheafData_flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem AlgebraicGeometry.IdealSheafData.flat_and_locallyOfFinitePresentation_subschemeInclusion_comp_of_forall_affineOpens_comap_eq_ker
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
        pt S' s Z ι hι hfl hfp = pt S' s Z' ι' hι' hfl' hfp' → ∃ e : Z ≅ Z', e.hom ≫ ι' = ι)

    (ZV : H.affineOpens → Scheme.{u})
      (ιV : ∀ V : H.affineOpens, ZV V ⟶ pullback f (V.2.fromSpec ≫ πH))
      (hclV : ∀ V : H.affineOpens, IsClosedImmersion (ιV V))
      (hflV : ∀ V : H.affineOpens, Flat (ιV V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
      (hfpV : ∀ V : H.affineOpens, LocallyOfFinitePresentation (ιV V ≫ pullback.snd f (V.2.fromSpec ≫ πH)))
      (jV : ∀ V : H.affineOpens, ZV V ⟶ ↑((pullback.snd f πH) ⁻¹ᵁ V.1))

      (htaut : ∀ V : H.affineOpens,
        pt Γ(H, V.1) (V.2.fromSpec ≫ πH) (ZV V) (ιV V) (hclV V) (hflV V) (hfpV V) = ⟨V.2.fromSpec, rfl⟩)

      (hjcl : ∀ V : H.affineOpens, IsClosedImmersion (jV V))
      (hjV : ∀ V : H.affineOpens,
        jV V ≫ ((pullback.snd f πH) ⁻¹ᵁ V.1).ι =
          ιV V ≫ pullback.map f (V.2.fromSpec ≫ πH) f πH (𝟙 X) V.2.fromSpec (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]))

      (hjfl : ∀ V : H.affineOpens, Flat (jV V ≫ (pullback.snd f πH) ∣_ V.1))
      (hjfp : ∀ V : H.affineOpens, LocallyOfFinitePresentation (jV V ≫ (pullback.snd f πH) ∣_ V.1))

      (hcompat : ∀ V V' : H.affineOpens,
        (jV V).ker.comap ((pullback f πH).homOfLE
            (inf_le_left : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V.1)) =
        (jV V').ker.comap ((pullback f πH).homOfLE
            (inf_le_right : (pullback.snd f πH) ⁻¹ᵁ V.1 ⊓ (pullback.snd f πH) ⁻¹ᵁ V'.1 ≤ (pullback.snd f πH) ⁻¹ᵁ V'.1)))
    (I₀ : (pullback f πH).IdealSheafData)
    (hI₀ : ∀ V : H.affineOpens, I₀.comap ((pullback.snd f πH) ⁻¹ᵁ V.1).ι = (jV V).ker) :
    Flat (I₀.subschemeι ≫ pullback.snd f πH) ∧ LocallyOfFinitePresentation (I₀.subschemeι ≫ pullback.snd f πH) := by sorry
