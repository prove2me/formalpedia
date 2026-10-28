-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_principal_localization_hom_of_fractionField
-- name    : AlgebraicGeometry.exists_principal_localization_hom_of_fractionField
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T14:58:00.49118+00:00
-- url     : https://prove2.me/theorems/fea98ca8-9768-4de4-afef-adb65e69e6eb
-- title:
--   Generic morphisms spread over a principal localization of the given affine base
-- statement:
--   Let $B$ be an integral domain with actual fraction field $E$. Let $X_1$ and $X_2$ be $B$-schemes such that $X_1\to\operatorname{Spec}B$ is quasi-compact and quasi-separated and $X_2\to\operatorname{Spec}B$ is locally of finite presentation. Every $E$-morphism
--   $$g:(X_1)_E\longrightarrow(X_2)_E$$
--   extends to a morphism over one principal localization: there exist $s\in B\setminus\{0\}$ and
--   $$g_s:(X_1)_{B[1/s]}\longrightarrow(X_2)_{B[1/s]}$$
--   whose pullback to $E$ is exactly $g$. The structure map $B[1/s]\to E$ is an actual injective $B$-algebra homomorphism; no abstract replacement of $E$ is made. Exact recovery is expressed for every pair of compatible comparison maps from the generic fibres to the localized fibres.
--
--   The result is universe polymorphic, works in arbitrary characteristic and needs no noetherian assumption on $B$. It supplies morphism spreading after constructing a smooth projective generic-fibre model, as needed for the Philippon alteration branch. It does not assert extension over all of $\operatorname{Spec}B$, descent of properness or surjectivity of $g$, or a global alteration.
-- source:
--   Auxiliary morphism spreading for the Philippon alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Reuses the Proved finite-stage morphism descent theorem https://prove2.me/theorems/562f2b15-890f-59cd-becd-dc283f5b9c98 (the noetherian approximation form of EGA IV 8.13.1), together with a direct finite-denominator argument in the actual fraction field. Complements the accepted smooth-family spreading construction https://prove2.me/theorems/a82deebd-f054-4a9f-bb40-7b01fbae3379 . The global covering family and semistable alteration remain separate.

import Mathlib
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.exists_principal_localization_hom_of_fractionField
    (B E : Type u) [CommRing B] [IsDomain B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (.of B)) (f₂ : X₂ ⟶ Spec (.of B))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₂]
    (g : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f₂ _ = pullback.snd f₁ _) :
    ∃ (s : B), s ≠ 0 ∧
      ∃ (γ : Localization.Away s →ₐ[B] E), Function.Injective γ ∧
        ∃ (g₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))) ⟶
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
          g₀ ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
          ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s)))))
            (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away s))))),
            q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
            q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
            q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom γ.toRingHom) →
            q₁ ≫ g₀ = g ≫ q₂ := by sorry
