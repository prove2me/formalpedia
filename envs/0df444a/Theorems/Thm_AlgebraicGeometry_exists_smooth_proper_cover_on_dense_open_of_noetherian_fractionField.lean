-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_proper_cover_on_dense_open_of_noetherian_fractionField
-- name    : AlgebraicGeometry.exists_smooth_proper_cover_on_dense_open_of_noetherian_fractionField
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T17:50:52.294729+00:00
-- url     : https://prove2.me/theorems/b80b7fa0-99ac-4810-898f-3410c104afe0
-- title:
--   Smooth proper generic covers spread over a noetherian base without a flatness assumption
-- statement:
--   Let $B$ be a noetherian integral domain with its actual fraction field $E$. Let $X_1$ and $X_2$ be $B$-schemes. Assume $X_1\to\operatorname{Spec}B$ is proper and locally of finite presentation, $X_2$ is quasi-compact, and $X_2\to\operatorname{Spec}B$ is separated and locally of finite presentation. Suppose $(X_1)_E$ is smooth over $E$ and there is a surjective $E$-morphism
--   $$g:(X_1)_E\longrightarrow(X_2)_E.$$
--
--   There is a dense open immersion $j:S\hookrightarrow\operatorname{Spec}B$ and actual base-change families $p_i:Y_i\to S$ with cartesian squares
--   $$\begin{matrix}Y_i&\xrightarrow{t_i}&X_i\\
--   \downarrow p_i&&\downarrow\\S&\xrightarrow{j}&\operatorname{Spec}B,\end{matrix}$$
--   such that $p_1$ is smooth and proper, $p_2$ is flat, and there is a proper surjective $S$-morphism
--   $$h:Y_1\longrightarrow Y_2.$$
--
--   The canonical map $\operatorname{Spec}E\to\operatorname{Spec}B$ factors through a map $b:\operatorname{Spec}E\to S$. There are cartesian comparison maps $e_i:(X_i)_E\to Y_i$ over $b$ such that $e_i$ followed by $t_i$ is exactly the original generic-fibre projection to $X_i$ and
--   $$e_1h=ge_2.$$
--   Thus the actual original generic cover is recovered, with its specified maps to the original models.
--
--   No flatness hypothesis is imposed on the original target family. The proof first makes it flat after principal base change. The statement is universe polymorphic and allows arbitrary characteristic and nonintegral or nonreduced source and target schemes. It supplies a smooth proper covering family over a dense base open, not a semistable compactification or a global smooth projective alteration.
-- source:
--   Auxiliary noetherian covering-family spreading for the Philippon alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Reuses the accepted scheme generic-flatness theorem https://prove2.me/theorems/535b0e9d-8abd-4406-a5b3-04bbf77128a4 and smooth covering-family theorem https://prove2.me/theorems/604920e5-4cba-4868-8bdc-68398a8edcb3 . Pure comparison and localization helpers retain the actual fraction field, the cartesian models and the original generic map. The proper source model is part of the input; constructing it from all finite-field curve data and performing semistable/global alteration remain separate.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.exists_smooth_proper_cover_on_dense_open_of_noetherian_fractionField
    (B E : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} [CompactSpace X₂]
    (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [IsProper f₁] [LocallyOfFinitePresentation f₁]
    [IsSeparated f₂] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) (hgs : Function.Surjective g)
    [Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))))] :
    ∃ (S : Scheme.{u}) (j : S ⟶ Spec (.of B)),
      IsOpenImmersion j ∧ DenseRange j ∧
      ∃ (Y₁ Y₂ : Scheme.{u}) (p₁ : Y₁ ⟶ S) (p₂ : Y₂ ⟶ S)
        (t₁ : Y₁ ⟶ X₁) (t₂ : Y₂ ⟶ X₂),
        IsPullback t₁ p₁ f₁ j ∧ IsPullback t₂ p₂ f₂ j ∧ Flat p₂ ∧
        ∃ (h : Y₁ ⟶ Y₂), h ≫ p₂ = p₁ ∧
          Smooth p₁ ∧ IsProper p₁ ∧ IsProper h ∧ Function.Surjective h ∧
          ∃ (b : Spec (.of E) ⟶ S)
            (e₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Y₁)
            (e₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Y₂),
            b ≫ j = Spec.map (CommRingCat.ofHom (algebraMap B E)) ∧
            IsPullback e₁ (pullback.snd f₁ _) p₁ b ∧
            IsPullback e₂ (pullback.snd f₂ _) p₂ b ∧
            e₁ ≫ t₁ = pullback.fst f₁ _ ∧ e₂ ≫ t₂ = pullback.fst f₂ _ ∧
            e₁ ≫ h = g ≫ e₂ := by sorry
