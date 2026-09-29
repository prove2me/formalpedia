-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
-- name    : AlgebraicGeometry.exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/cb069eb7-fdce-5dbf-9689-bb1d3916853f
-- title:
--   Descent of an isomorphism of base changes to a finitely generated subalgebra
-- statement:
--   Let $A_0$ be a commutative ring and $A$ a commutative $A_0$-algebra (both in a fixed universe), let $X_1, X_2$ be schemes, and let $f_1\colon X_1 \to \operatorname{Spec} A_0$ and $f_2\colon X_2 \to \operatorname{Spec} A_0$ be morphisms, each assumed quasi-compact, quasi-separated and locally of finite presentation. Write $\operatorname{Spec} A \to \operatorname{Spec} A_0$ for the morphism induced by the structure map $A_0 \to A$, and suppose given an isomorphism $e$ between the fibre products $X_1 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ and $X_2 \times_{\operatorname{Spec} A_0} \operatorname{Spec} A$ which is compatible with the second projections, i.e. $e$ followed by the projection to $\operatorname{Spec} A$ is the projection to $\operatorname{Spec} A$. Then for every finite subset $s \subseteq A$ there exist a finitely generated $A_0$-subalgebra $T \subseteq A$ with $s \subseteq T$ and an isomorphism $e_0$ between $X_1 \times_{\operatorname{Spec} A_0} \operatorname{Spec} T$ and $X_2 \times_{\operatorname{Spec} A_0} \operatorname{Spec} T$, again compatible with the projections to $\operatorname{Spec} T$, such that $e_0$ recovers $e$ after base change in the following sense: whenever $q_1$ and $q_2$ are morphisms from the $A$-base changes of $X_1$, respectively $X_2$, to their $T$-base changes which commute with the projections to $X_1$, resp. $X_2$, and whose composites with the projections to $\operatorname{Spec} T$ equal the projections to $\operatorname{Spec} A$ followed by the morphism $\operatorname{Spec} A \to \operatorname{Spec} T$ induced by the inclusion $T \hookrightarrow A$, one has $e_0 \circ q_1 = q_2 \circ e$.
--
--   This is the scheme-theoretic limit-approximation statement that an isomorphism between the base changes to $A$ of two finitely presented $A_0$-schemes already descends to some finitely generated $A_0$-subalgebra of $A$, in the form of EGA IV₃ §8. It is obtained from the corresponding descent statement for a single morphism over $\operatorname{Spec} A$ applied to $e$ and its inverse together with the rigidity statement for morphisms locally of finite type, and it feeds the gluing of such descents over an open cover and the approximation arguments for the standard isomorphism packages of fake elliptic curves in the Čerednik–Drinfeld part of the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_fg_subalgebra_iso_pullback_of_iso_pullback_of_locallyOfFinitePresentation
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {X₁ X₂ : Scheme.{u}} (f₁ : X₁ ⟶ Spec (CommRingCat.of A₀)) (f₂ : X₂ ⟶ Spec (CommRingCat.of A₀))
    [QuasiCompact f₁] [QuasiSeparated f₁] [LocallyOfFinitePresentation f₁]
    [QuasiCompact f₂] [QuasiSeparated f₂] [LocallyOfFinitePresentation f₂]
    (e : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ≅
      pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))))
    (he : e.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _) (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∃ e₀ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ≅
          pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        e₀.hom ≫ pullback.snd f₂ _ = pullback.snd f₁ _ ∧
        ∀ (q₁ : pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₁ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))))
          (q₂ : pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
              pullback f₂ (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T)))),
          q₁ ≫ pullback.fst f₁ _ = pullback.fst f₁ _ →
          q₁ ≫ pullback.snd f₁ _ = pullback.snd f₁ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₂ ≫ pullback.fst f₂ _ = pullback.fst f₂ _ →
          q₂ ≫ pullback.snd f₂ _ = pullback.snd f₂ _ ≫ Spec.map (CommRingCat.ofHom T.val.toRingHom) →
          q₁ ≫ e₀.hom = e.hom ≫ q₂ := by sorry
