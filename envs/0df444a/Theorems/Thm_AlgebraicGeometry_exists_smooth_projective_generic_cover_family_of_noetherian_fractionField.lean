-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_smooth_projective_generic_cover_family_of_noetherian_fractionField
-- name    : AlgebraicGeometry.exists_smooth_projective_generic_cover_family_of_noetherian_fractionField
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-25T18:38:45.928738+00:00
-- url     : https://prove2.me/theorems/9d194c42-8928-4185-90b1-2e9ba53665ea
-- title:
--   A smooth projective generic cover spreads to an actual covering family
-- statement:
--   Let $B$ be a noetherian integral domain with its actual fraction field $E$, and let $f:X\to\operatorname{Spec}B$ be proper and locally of finite presentation. Let $C$ be a smooth projective $E$-scheme with a specified closed immersion into $\mathbb P^n_E$, and let
--   $$g:C\longrightarrow X_E$$
--   be a surjective $E$-morphism to the actual generic fibre.
--
--   There are a nonzero $a\in B$, an injective $B$-algebra map $A=B[1/a]\to E$, and a projective model $M\hookrightarrow\mathbb P^n_A$ with the given $C$ as its exact generic pullback. There is a dense open immersion $j:S\hookrightarrow\operatorname{Spec}A$, a smooth proper family $Y\to S$ obtained by base change of $M$, and the flat proper target family $Z=X\times_{\operatorname{Spec}B}S$, together with a proper surjective $S$-morphism
--   $$h:Y\longrightarrow Z.$$
--   Both base-change squares are retained as actual cartesian squares; the projective ambient model of $Y$ is retained as well.
--
--   The given map from $\operatorname{Spec}E$ to $\operatorname{Spec}A$ factors through $S$. There are cartesian comparison maps $e_C:C\to Y$ and $e_X:X_E\to Z$ such that $e_C$ followed by the map to $M$ is exactly the specified generic model map, $e_X$ followed by the map to $X$ is exactly the original generic-fibre projection, and
--   $$e_Ch=ge_X.$$
--   The theorem therefore constructs the proper projective source model and the covering family starting with the actual smooth projective generic cover, without assuming a pre-existing source family or target flatness.
--
--   The result is universe polymorphic and permits arbitrary characteristic. It supplies the smooth projective covering family over a dense base open needed in the Philippon alteration branch; it does not construct a semistable compactification or a global smooth projective alteration.
-- source:
--   Auxiliary generic-cover spreading construction for the Philippon alteration frontier https://prove2.me/theorems/842dbd70-6333-40fa-86df-02394eb67249 . Uses the accepted noetherian covering-family theorem https://prove2.me/theorems/b80b7fa0-99ac-4810-898f-3410c104afe0 , Proved projective approximation https://prove2.me/theorems/44445023-0444-5411-b136-0fd554f8e11d , and Proved base change of projective embeddings https://prove2.me/theorems/899d38bc-8ead-534b-ac8b-ae36d35999c7 . The flat projective-model construction reuses the checked source of https://prove2.me/theorems/a82deebd-f054-4a9f-bb40-7b01fbae3379 and retains its actual coefficient maps. The finite-field base construction and semistable/global alteration are separate.

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.exists_smooth_projective_generic_cover_family_of_noetherian_fractionField
    (B E : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [Field E]
    [Algebra B E] [IsFractionRing B E]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of B)) [IsProper f] [LocallyOfFinitePresentation f]
    (C : Scheme.{u}) (n : ℕ)
    (ι : C ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) E))
    [IsClosedImmersion ι] [Smooth (ι ≫ ProjSpace.π E n)]
    (g : C ⟶ pullback f (Spec.map (CommRingCat.ofHom (algebraMap B E))))
    (hg : g ≫ pullback.snd f _ = ι ≫ ProjSpace.π E n) (hgs : Function.Surjective g) :
    ∃ a : B, a ≠ 0 ∧
      ∃ γ : Localization.Away a →ₐ[B] E, Function.Injective γ ∧
        ∃ (M : Scheme.{u})
          (iM : M ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (Localization.Away a)))
          (gM : C ⟶ M), IsClosedImmersion iM ∧
          IsPullback gM (ι ≫ ProjSpace.π E n) (iM ≫ ProjSpace.π (Localization.Away a) n)
            (Spec.map (CommRingCat.ofHom γ.toRingHom)) ∧
          ∃ (S : Scheme.{u}) (j : S ⟶ Spec (.of (Localization.Away a))),
            IsOpenImmersion j ∧ DenseRange j ∧
            ∃ (Y Z : Scheme.{u}) (pY : Y ⟶ S) (pZ : Z ⟶ S) (tY : Y ⟶ M) (tZ : Z ⟶ X),
              IsPullback tY pY (iM ≫ ProjSpace.π (Localization.Away a) n) j ∧
              IsPullback tZ pZ f (j ≫ Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away a)))) ∧
              Smooth pY ∧ IsProper pY ∧ Flat pZ ∧ IsProper pZ ∧
              ∃ h : Y ⟶ Z, h ≫ pZ = pY ∧ IsProper h ∧ Function.Surjective h ∧
                ∃ (b : Spec (.of E) ⟶ S) (eC : C ⟶ Y)
                  (eX : pullback f (Spec.map (CommRingCat.ofHom (algebraMap B E))) ⟶ Z),
                  b ≫ j = Spec.map (CommRingCat.ofHom γ.toRingHom) ∧
                  IsPullback eC (ι ≫ ProjSpace.π E n) pY b ∧
                  IsPullback eX (pullback.snd f _) pZ b ∧
                  eC ≫ tY = gM ∧ eX ≫ tZ = pullback.fst f _ ∧ eC ≫ h = g ≫ eX := by sorry
