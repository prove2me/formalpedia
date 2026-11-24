-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_proper_finitePresentation_envelope_with_noetherian_baseChange
-- name    : AlgebraicGeometry.Scheme.exists_proper_finitePresentation_envelope_with_noetherian_baseChange
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T19:49:50.610219+00:00
-- url     : https://prove2.me/theorems/2f68adc4-3425-434d-a36b-82968956fe72
-- title:
--   A proper finitely presented envelope preserving a Noetherian base change
-- statement:
--   Let $A$ be a commutative ring, $X$ proper over $\operatorname{Spec}(A)$ and $S\to\operatorname{Spec}(A)$ a morphism from a Noetherian scheme. There is a closed immersion $X\hookrightarrow P$ over $\operatorname{Spec}(A)$ with $P$ proper and finitely presented and $X\times_A S\to P\times_A S$ an isomorphism.
-- source:
--   Prescribed-base-change consequence of the proper approximation in the Stacks Project, Lemma 32.13.2.

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.exists_proper_finitePresentation_envelope_with_noetherian_baseChange {A : Type u} [CommRing A] {X S T : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (r : S ⟶ Spec (.of A)) [IsNoetherian S]
    (s : T ⟶ S) (j : T ⟶ X) (h : IsPullback s j r f) :
    ∃ (P : Scheme.{u}) (g : P ⟶ Spec (.of A)) (a : X ⟶ P),
      IsProper g ∧ LocallyOfFinitePresentation g ∧ IsClosedImmersion a ∧
        a ≫ g = f ∧ IsPullback s (j ≫ a) r g := by sorry
