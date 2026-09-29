-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
-- name    : AlgebraicGeometry.Polarisation.ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/008fb0b7-81d1-5ac6-b650-68c4ce87f934
-- title:
--   Base change of theta points along a cartesian square
-- statement:
--   Let $\varphi : S \to S'$ be a homomorphism of commutative rings, let $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} S'$ be morphisms of schemes carrying relative group laws $L$, $L'$ (functorial group structures on the sets $\{x : T \to A \mid x \circ f = t\}$ of points over a base morphism $t$), and let $g_A : A' \to A$ be such that the square formed by $g_A$, $f'$, $f$ and $\operatorname{Spec}\varphi$ is cartesian, and such that $g_A$ is multiplicative on points: for every scheme $T$, every $t'' : T \to \operatorname{Spec} S'$ and all points $x, y$ of $A'$ over $t''$, the composite of $L'.\mathrm{mul}\,t''\,x\,y$ with $g_A$ is $L.\mathrm{mul}$ over $t''$ followed by $\operatorname{Spec}\varphi$ of the composites $x \circ g_A$, $y \circ g_A$. Let $\mathcal L$ be a module on $A$ and $\mathcal L'$ a module on $A'$ (no invertibility is assumed), let $t : \operatorname{Spec} R \to \operatorname{Spec} S$ and $t' : \operatorname{Spec} R' \to \operatorname{Spec} S'$ be test morphisms, and let $\psi : R \to R'$ satisfy $\operatorname{Spec}\psi$ followed by $t$ $=$ $t'$ followed by $\operatorname{Spec}\varphi$. Let $b : A' \times_{\operatorname{Spec} S'} \operatorname{Spec} R' \to A \times_{\operatorname{Spec} S} \operatorname{Spec} R$ be a morphism with $b$ followed by the first projection equal to the first projection followed by $g_A$, and $b$ followed by the second projection equal to the second projection followed by $\operatorname{Spec}\psi$, and let $c$ be an isomorphism of modules $b^{*}\mathrm{pr}_1^{*}\mathcal L \cong \mathrm{pr}_1'^{*}\mathcal L'$. Then there exists a monoid homomorphism $\beta$ from `ThetaPt f L 𝓛 t` to `ThetaPt f' L' 𝓛' t'` — where a theta point consists of a point $\mathrm{pt}$ of $A$ over $t$ together with an isomorphism between the pullback of $\mathrm{pr}_1^{*}\mathcal L$ along translation by $\mathrm{pt}$ and $\mathrm{pr}_1^{*}\mathcal L$ itself, multiplied as in [`AlgebraicGeometry.Polarisation.ThetaPt.mul`](def/AlgebraicGeometry_ThetaGroupLaw.html#L230) — such that: (i) for every $\theta$, the underlying point of $\beta\theta$ composed with $g_A$ equals $\operatorname{Spec}\psi$ followed by the underlying point of $\theta$; (ii) for every $\theta$ and every global section $s$ of $\mathrm{pr}_1^{*}\mathcal L$, the operator $(\beta\theta).\mathrm{act}$ applied to $c(b^{*}s)$ equals $c(b^{*}(\theta.\mathrm{act}\,s))$, where $b^{*}$ is the adjunction-unit map on local sections `Scheme.Modules.pullbackLocalSection`; (iii) $\beta(\mathrm{ofScalar}\,u) = \mathrm{ofScalar}(\psi u)$ for every unit $u \in R^{\times}$; and (iv) $\beta(\mathrm{ofUnit}\,v) = \mathrm{ofUnit}(b^{\sharp}v)$ for every unit $v$ of the ring of global sections of $A \times_{\operatorname{Spec} S} \operatorname{Spec} R$, $b^{\sharp}$ being the map induced by $b$ on global sections.
--
--   This is the functoriality of Mumford's theta group $\mathcal G(\mathcal L)$ under base change, in the concrete form needed here: a morphism of cartesian squares together with a comparison isomorphism of the pulled-back modules induces a multiplicative map on theta points compatible with the underlying points, the action on global sections, and the scalar and unit sections. It is used in the construction and verification of theta-adapted framed polarised abelian schemes and in the comparison homomorphism attached to a ring homomorphism.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_ThetaPt_exists_monoidHom_pt_comp_eq_act_eq_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ThetaGroupLaw

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.ThetaPt.exists_monoidHom_pt_comp_eq_act_eq_of_isPullback
    {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S')
    {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of S')}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw S' f')
    (gA : A' ⟶ A) (hg : CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T : Scheme.{0}} (t'' : T ⟶ Spec (CommRingCat.of S')) (x y : SchemeHomOver t'' f'),
      (L'.mul t'' x y).1 ≫ gA =
        (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (𝓛 : A.Modules) (𝓛' : A'.Modules)
    {R R' : Type} [CommRing R] [CommRing R'] (t : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of S))
    (t' : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of S')) (ψ : R →+* R')
    (hr : Spec.map (CommRingCat.ofHom ψ) ≫ t = t' ≫ Spec.map (CommRingCat.ofHom φ))
    (b : pullback f' t' ⟶ pullback f t) (hb₁ : b ≫ pullback.fst f t = pullback.fst f' t' ≫ gA)
    (hb₂ : b ≫ pullback.snd f t = pullback.snd f' t' ≫ Spec.map (CommRingCat.ofHom ψ))
    (c : (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛) ≅
      (Scheme.Modules.pullback (pullback.fst f' t')).obj 𝓛') :
    ∃ β : ThetaPt f L 𝓛 t →* ThetaPt f' L' 𝓛' t',
      (∀ θ : ThetaPt f L 𝓛 t, (β θ).pt.1 ≫ gA = Spec.map (CommRingCat.ofHom ψ) ≫ θ.pt.1) ∧
      (∀ (θ : ThetaPt f L 𝓛 t) (s : Γ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛, ⊤)),
        (β θ).act (c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b s :
            Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) =
          c.hom.app ⊤ (Scheme.Modules.pullbackLocalSection b (θ.act s) :
            Γ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback (pullback.fst f t)).obj 𝓛), ⊤))) ∧
      (∀ u : Rˣ, β (ThetaPt.ofScalar u) = ThetaPt.ofScalar (Units.map (ψ : R →* R') u)) ∧
      (∀ v : Γ(pullback f t, ⊤)ˣ,
        β (ThetaPt.ofUnit v) = ThetaPt.ofUnit (Units.map (b.appTop.hom : Γ(pullback f t, ⊤) →* Γ(pullback f' t', ⊤)) v)) := by sorry
