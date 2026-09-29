-- Prove2me | Theorems.Thm_AlgebraicGeometry_Polarisation_exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback
-- name    : AlgebraicGeometry.Polarisation.exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:44.354383+00:00
-- url     : https://prove2.me/theorems/2e864c8f-cd87-52c3-a0d7-fc77053bdadf
-- title:
--   Translations are compatible with base change along Specφ
-- statement:
--   Let $S,T$ be commutative rings and $\varphi : S \to T$ a ring homomorphism, let $A, A'$ be schemes with structure morphisms $f : A \to \operatorname{Spec} S$ and $f' : A' \to \operatorname{Spec} T$, and let $L$, $L'$ be relative group laws on $f$ and on $f'$, that is, group structures on the sets $\{\psi : T'' \to A \mid \psi \circ f = t\}$ of sections over each test morphism, natural in the test scheme. Assume given $g_A : A' \to A$ such that the square formed by $g_A$, $f'$, $f$ and $\operatorname{Spec}\varphi$ is cartesian, and assume $g_A$ is multiplicative: for every scheme $T''$, every $t'' : T'' \to \operatorname{Spec} T$ and all sections $x,y$ of $f'$ over $t''$, the section $L'.\mathrm{mul}\,t''\,x\,y$ followed by $g_A$ equals the $L$-product, over $t''$ followed by $\operatorname{Spec}\varphi$, of $x$ followed by $g_A$ and $y$ followed by $g_A$. Finally let $x_0$ be a section of $f$ over $\mathrm{id}_{\operatorname{Spec} S}$ and $x$ a section of $f'$ over $\mathrm{id}_{\operatorname{Spec} T}$ with $x$ followed by $g_A$ equal to $\operatorname{Spec}\varphi$ followed by $x_0$. Then there is a morphism $\kappa$ from $A' \times_{\operatorname{Spec} T} \operatorname{Spec} T$ (the pullback of $f'$ along the identity) to the pullback of the second projection $A \times_{\operatorname{Spec} S} \operatorname{Spec} S \to \operatorname{Spec} S$ along $\operatorname{Spec}\varphi$ such that $\kappa$ is an isomorphism, $\kappa$ followed by the first projection and then by the projection to $A$ equals the projection to $A'$ followed by $g_A$, and the translation endomorphism $\mathrm{translate}\,f'\,L'\,\mathrm{id}\,x$ followed by $\kappa$ and the first projection equals $\kappa$, the first projection and then $\mathrm{translate}\,f\,L\,\mathrm{id}\,x_0$, where $\mathrm{translate}\,f\,L\,t\,y$ denotes the endomorphism of $\mathrm{pullback}\,f\,t$ obtained by multiplying the tautological section with the pullback of $y$.
--
--   This is the base-change compatibility of translation by a section: the two descriptions of $A'\times_{\operatorname{Spec} T}\operatorname{Spec} T$ as a fibre product over $\operatorname{Spec} S$ are identified, and under that identification translation by $x$ on the $T$-side corresponds to translation by $x_0$ on the $S$-side. It is used in the analysis of when a theta-type equation $\tau_x \circ (\cdot) = (\cdot)$ persists under base change for framed polarised abelian schemes, via [`AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_translate_comp_eq_iff_map_eq_bot_of_section`](thm.html#AlgebraicGeometry.FramedPolarisedAbelianScheme.exists_ideal_fg_forall_isPullback_translate_comp_eq_iff_map_eq_bot_of_section).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Polarisation_exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback.lean

import Definitions.Def_AlgebraicGeometry_ThetaAdaptedFrame

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.exists_isIso_comp_fst_comp_fst_eq_and_translate_comp_eq_of_isPullback
    {S T : Type} [CommRing S] [CommRing T] (φ : S →+* T)
    {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} {f' : A' ⟶ Spec (CommRingCat.of T)}
    (L : RelativeGroupLaw S f) (L' : RelativeGroupLaw T f')
    (gA : A' ⟶ A) (hg : CategoryTheory.IsPullback gA f' f (Spec.map (CommRingCat.ofHom φ)))
    (hmul : ∀ {T'' : Scheme.{0}} (t'' : T'' ⟶ Spec (CommRingCat.of T)) (x y : SchemeHomOver t'' f'),
      (L'.mul t'' x y).1 ≫ gA =
        (L.mul (t'' ≫ Spec.map (CommRingCat.ofHom φ))
          ⟨x.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, x.2]⟩
          ⟨y.1 ≫ gA, by rw [Category.assoc, hg.w, ← Category.assoc, y.2]⟩).1)
    (x₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of T))) f')
    (hx : x.1 ≫ gA = Spec.map (CommRingCat.ofHom φ) ≫ x₀.1) :
    ∃ κ : pullback f' (𝟙 (Spec (CommRingCat.of T))) ⟶
        pullback (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)),
      IsIso κ ∧
      κ ≫ pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ≫
          pullback.fst f (𝟙 (Spec (CommRingCat.of S))) =
        pullback.fst f' (𝟙 (Spec (CommRingCat.of T))) ≫ gA ∧
      Polarisation.translate f' L' (𝟙 (Spec (CommRingCat.of T))) x ≫ κ ≫
          pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) =
        κ ≫ pullback.fst (pullback.snd f (𝟙 (Spec (CommRingCat.of S)))) (Spec.map (CommRingCat.ofHom φ)) ≫
          Polarisation.translate f L (𝟙 (Spec (CommRingCat.of S))) x₀ := by sorry
