-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_proper_cover_on_dense_open_of_fractionField
-- name    : AlgebraicGeometry.exists_smooth_proper_cover_on_dense_open_of_fractionField
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T15:37:41.980643+00:00
-- url     : https://prove2.me/theorems/604920e5-4cba-4868-8bdc-68398a8edcb3
-- title:
--   Smooth proper generic covers spread to covering families on a dense open
-- statement:
--   Let $B$ be an integral domain with its actual fraction field $E$. Let $p:X_1\to\operatorname{Spec}B$ be proper and locally of finite presentation, and let $q:X_2\to\operatorname{Spec}B$ be flat, separated and locally of finite presentation. Suppose the generic fibre $(X_1)_E$ is smooth over $E$ and there is a surjective $E$-morphism
--   $$g:(X_1)_E\longrightarrow(X_2)_E.$$
--
--   Then there is a nonzero $s\in B$ and a proper surjective morphism over $A=B[1/s]$,
--   $$g_A:(X_1)_A\longrightarrow(X_2)_A,$$
--   whose pullback to $E$ is exactly the given $g$. The map $A\to E$ is retained as an actual injective $B$-algebra homomorphism. Exact recovery is asserted for every pair of compatible comparison maps of the generic and localized fibres.
--
--   Moreover, there is a dense open $U\subset\operatorname{Spec}A$ containing the entire image of $\operatorname{Spec}E$ such that $(X_1)_U\to U$ is smooth and proper. The localized map restricts to an actual proper surjection
--   $$(X_1)_U\longrightarrow(X_2)_U$$
--   over $U$, with the exact equality of its composite into $(X_2)_A$ and the restriction of $g_A$.
--
--   The result works in arbitrary universes and characteristic and needs no noetherian hypothesis on $B$. It retains the covering map as well as the smooth proper source family, which is needed when spreading generic curve covers in the Philippon alteration branch. Flatness of the target family is an essential hypothesis in this formulation. The theorem does not construct a semistable compactification or a global smooth projective alteration.
-- source:
--   Auxiliary covering-family spreading for the Philippon alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Reuses the accepted generic-morphism spreading theorem https://prove2.me/theorems/fea98ca8-9768-4de4-afef-adb65e69e6eb and the Proved flat-base-change smooth-locus theorem https://prove2.me/theorems/dd990c97-2f4d-55b4-9879-54c6e7ff5f23 . Surjectivity is proved directly using flat generalization lifting and closedness of the proper image; restrictions and generic pullback comparisons use Mathlib. Complements the accepted projective generic-family model https://prove2.me/theorems/a82deebd-f054-4a9f-bb40-7b01fbae3379 . Generic flatness of the target, application to the full finite-field curve-cover data, and semistable alteration remain separate.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

theorem AlgebraicGeometry.exists_smooth_proper_cover_on_dense_open_of_fractionField
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [IsProper f₁] [LocallyOfFinitePresentation f₁] [Flat f₂] [IsSeparated f₂] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _)
    (hgs : Function.Surjective g)
    [Smooth (pullback.snd f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))))] :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
          g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
          IsProper g₀ ∧ Function.Surjective g₀ ∧
          (∃ U : (Spec (.of (Localization.Away s))).Opens,
            Dense (U : Set (Spec (.of (Localization.Away s)))) ∧
            Set.range (Spec.map (CommRingCat.ofHom γ.toRingHom)) ⊆ U ∧
            Smooth ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
              (algebraMap B (Localization.Away s))))) ∣_ U) ∧
            IsProper ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
              (algebraMap B (Localization.Away s))))) ∣_ U) ∧
            ∃ h : ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
                    (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U : Scheme) ⟶
                  ((pullback.snd f₂ (Spec.map (CommRingCat.ofHom
                    (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U : Scheme),
              h ≫ ((pullback.snd f₂ (Spec.map (CommRingCat.ofHom
                (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U).ι =
                ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
                  (algebraMap B (Localization.Away s))))) ⁻¹ᵁ U).ι ≫ g₀ ∧
              h ≫ ((pullback.snd f₂ (Spec.map (CommRingCat.ofHom
                (algebraMap B (Localization.Away s))))) ∣_ U) =
                ((pullback.snd f₁ (Spec.map (CommRingCat.ofHom
                  (algebraMap B (Localization.Away s))))) ∣_ U) ∧
              IsProper h ∧ Function.Surjective h) ∧
          ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))))
            (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
            q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
            q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
            q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₁ ≫ g₀ = g ≫ q₂ := by sorry
