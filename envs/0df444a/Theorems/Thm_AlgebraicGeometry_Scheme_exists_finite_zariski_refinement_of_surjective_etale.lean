-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_zariski_refinement_of_surjective_etale
-- name    : AlgebraicGeometry.Scheme.exists_finite_zariski_refinement_of_surjective_etale
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T07:15:50.25253+00:00
-- url     : https://prove2.me/theorems/16b5d5ba-402b-4c1d-ba3b-15b2c6df5362
-- title:
--   Finite Zariski refinement of a surjective étale morphism
-- statement:
--   Let $U \to X$ be surjective and étale, with $X$ quasi-compact and quasi-separated. There is a finite surjective morphism $P \to X$ that factors Zariski locally through $U \to X$.
-- source:
--   Stacks Project, Lemma 37.45.7, https://stacks.math.columbia.edu/tag/09Z0.

import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.exists_finite_zariski_refinement_of_surjective_etale {U X : Scheme.{u}} [SpectralSpace X]
    (f : U ⟶ X) [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ X), IsFinite p ∧ Surjective p ∧
      ∀ x : P, ∃ (W : Scheme.{u}) (i : W ⟶ P), IsOpenImmersion i ∧ x ∈ Set.range i ∧
        ∃ g : W ⟶ U, g ≫ f = i ≫ p := by sorry
