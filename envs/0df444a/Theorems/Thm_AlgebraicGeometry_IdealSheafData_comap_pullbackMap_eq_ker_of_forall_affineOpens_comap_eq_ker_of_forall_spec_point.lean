-- Prove2me | Theorems.Thm_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point
-- name    : AlgebraicGeometry.IdealSheafData.comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/e2dc34e0-ccd4-50f3-b9cd-50c79553d2b1
-- title:
--   Comap of the glued ideal sheaf along a classifying map
-- statement:
--   Let $S$ be a commutative ring, $X,H$ schemes, and $f : X \to \operatorname{Spec} S$, $\pi_H : H \to \operatorname{Spec} S$ morphisms. Suppose given an assignment `pt` which, for every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every closed immersion $\iota : Z \to X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ whose composite with the second projection is flat and locally of finite presentation, produces a pair consisting of a morphism $\operatorname{Spec} S' \to H$ together with a proof that it becomes $s$ after composing with $\pi_H$; and suppose `pt` is compatible with base change along ring maps $\psi : S' \to S''$ in the sense made precise by `hnat` (for pullback squares of the flat subschemes compatible with the induced map of pullbacks, the value at the base-changed datum is $\operatorname{Spec}(\psi)$ followed by the value at the original), is surjective onto such pairs (`hsurj`), and is injective up to an isomorphism of the closed subschemes over the pullback (`hinj`). Suppose further given, for each affine open $V$ of $H$, a scheme $Z_V$ with a closed immersion $\iota_V$ into $X \times_{\operatorname{Spec} S} \operatorname{Spec} \Gamma(H,V)$, flat and locally of finite presentation over that base, whose `pt`-value is the tautological pair $(\operatorname{Spec}\Gamma(H,V) \to H, \mathrm{rfl})$, together with a closed immersion $j_V : Z_V \to (\mathrm{pr}_2)^{-1}(V)$ into the open subscheme of $X \times_{\operatorname{Spec} S} H$ over $V$ which is flat and locally of finite presentation over $V$ and which, composed with the open immersion, equals $\iota_V$ followed by the map of pullbacks induced by $\mathrm{id}_X$ and $\operatorname{Spec}\Gamma(H,V) \to H$; assume the ideal sheaves $\ker j_V$ and $\ker j_{V'}$ agree after comap to $(\mathrm{pr}_2)^{-1}(V) \cap (\mathrm{pr}_2)^{-1}(V')$. Finally let $I_0$ be an ideal sheaf datum on $X \times_{\operatorname{Spec} S} H$ whose comap along each open immersion $(\mathrm{pr}_2)^{-1}(V) \to X \times_{\operatorname{Spec} S} H$ is $\ker j_V$. Then for every $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every closed immersion $\iota_Z : Z \to X \times_{\operatorname{Spec} S} \operatorname{Spec} S'$ flat and locally of finite presentation over $\operatorname{Spec} S'$, the comap of $I_0$ along the morphism $X \times_{\operatorname{Spec} S} \operatorname{Spec} S' \to X \times_{\operatorname{Spec} S} H$ induced by $\mathrm{id}_X$ and the first component of $\mathrm{pt}(S',s,Z,\iota_Z)$ equals $\ker \iota_Z$.
--
--   This is the ideal-sheaf comparison clause in a Hilbert-scheme style universal property: the ideal sheaf glued from the local data $\ker j_V$ over the affine opens of $H$ pulls back, along the classifying map attached by `pt` to any flat, locally finitely presented closed subscheme of a base change of $X$, to the ideal sheaf of that subscheme. It is used by [`AlgebraicGeometry.exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq`](thm.html#AlgebraicGeometry.exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_IdealSheafData_comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem AlgebraicGeometry.IdealSheafData.comap_pullbackMap_eq_ker_of_forall_affineOpens_comap_eq_ker_of_forall_spec_point
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
    ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
      (Z : Scheme.{u}) (ιZ : Z ⟶ pullback f s) (hι : IsClosedImmersion ιZ) (hfl : Flat (ιZ ≫ pullback.snd f s))
      (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd f s)),
      I₀.comap (pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2])) = ιZ.ker := by sorry
