-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq
-- name    : AlgebraicGeometry.exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.195734+00:00
-- url     : https://prove2.me/theorems/67348916-9331-5a94-8046-fd04185bb94a
-- title:
--   Glued ideal sheaf yields the universal flat closed subscheme
-- statement:
--   Let $S$ be a commutative ring, $X,H$ schemes, and $f : X \to \operatorname{Spec} S$, $\pi_H : H \to \operatorname{Spec} S$ morphisms; write $p =$ `pullback.snd f πH` for the projection $X \times_S H \to H$. Assume given an assignment `pt` sending each commutative ring $S'$, each $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and each closed immersion $\iota : Z \hookrightarrow X \times_S \operatorname{Spec} S'$ whose composite with the projection to $\operatorname{Spec} S'$ is flat and locally of finite presentation to a pair consisting of a morphism $\operatorname{Spec} S' \to H$ together with a proof that its composite with $\pi_H$ is $s$; assume `pt` is compatible with base change along ring maps $\psi : S' \to S''$ in the sense of `hnat`, that every such pair over $s$ is attained (`hsurj`), and that two such closed subschemes with the same value under `pt` are isomorphic over $X \times_S \operatorname{Spec} S'$ (`hinj`). Assume further, for each affine open $V \subseteq H$ with ring $\Gamma(H,V)$: a scheme $Z_V$, a closed immersion $\iota_V : Z_V \to X \times_S V$ flat and locally of finite presentation over $V$ whose value under `pt` is the tautological pair $\langle$`V.2.fromSpec`$, \mathrm{rfl}\rangle$, and a closed immersion $j_V : Z_V \to p^{-1}(V)$ compatible with $\iota_V$ under the open immersion $p^{-1}(V) \hookrightarrow X \times_S H$, with $j_V$ followed by $p|_V$ flat and locally of finite presentation, and with the ideal sheaves $\ker(j_V)$ agreeing after restriction to $p^{-1}(V) \cap p^{-1}(V')$ for all affine opens $V,V'$. Finally let $I_0$ be an ideal sheaf datum on $X \times_S H$ whose pullback along each open immersion $p^{-1}(V) \hookrightarrow X \times_S H$ is $\ker(j_V)$. Then there exist a scheme $\mathcal Z$ and a closed immersion $\iota : \mathcal Z \to X \times_S H$ such that $\iota$ followed by $p$ is flat and locally of finite presentation, and such that for every commutative ring $S'$, every $s : \operatorname{Spec} S' \to \operatorname{Spec} S$ and every closed immersion $\iota_Z : Z \to X \times_S \operatorname{Spec} S'$ flat and locally of finite presentation over $\operatorname{Spec} S'$ there is $e : Z \to \mathcal Z$ making $Z$ the fibre product of $\mathcal Z \to H$ and the morphism $\operatorname{Spec} S' \to H$ attached by `pt`, compatibly with the closed immersions, i.e. $\iota_Z$ followed by the induced map $X \times_S \operatorname{Spec} S' \to X \times_S H$ equals $e$ followed by $\iota$.
--
--   This is the gluing step in the construction of the universal flat, finitely presented closed subscheme of $X \times_S H$ over a scheme $H$ representing the relevant Hilbert-type functor: the locally given subschemes $Z_V \subseteq p^{-1}(V)$ are assembled into one closed subscheme via the ideal sheaf datum $I_0$, and the resulting subscheme is shown to have the universal base-change property. It is used by [`AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point`](thm.html#AlgebraicGeometry.exists_closedSubscheme_pullback_flat_forall_isPullback_of_forall_spec_point), part of the scheme-theoretic infrastructure supporting Néron models and good reduction of Jacobians in this development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
universe u

theorem AlgebraicGeometry.exists_closedSubscheme_pullback_flat_of_idealSheafData_comap_ker_eq
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
    ∃ (𝒵 : Scheme.{u}) (ι : 𝒵 ⟶ pullback f πH), IsClosedImmersion ι ∧ Flat (ι ≫ pullback.snd f πH) ∧
      LocallyOfFinitePresentation (ι ≫ pullback.snd f πH) ∧
      ∀ (S' : Type u) [CommRing S'] (s : Spec (CommRingCat.of S') ⟶ Spec (CommRingCat.of S))
        (Z : Scheme.{u}) (ιZ : Z ⟶ pullback f s) (hι : IsClosedImmersion ιZ) (hfl : Flat (ιZ ≫ pullback.snd f s))
        (hfp : LocallyOfFinitePresentation (ιZ ≫ pullback.snd f s)),
        ∃ e : Z ⟶ 𝒵,
          IsPullback e (ιZ ≫ pullback.snd f s) (ι ≫ pullback.snd f πH) (pt S' s Z ιZ hι hfl hfp).1 ∧
          ιZ ≫ pullback.map f s f πH (𝟙 X) (pt S' s Z ιZ hι hfl hfp).1 (𝟙 _)
              (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, (pt S' s Z ιZ hι hfl hfp).2]) = e ≫ ι := by sorry
