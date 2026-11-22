-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_integral_zariski_refinement_of_surjective_etale
-- name    : AlgebraicGeometry.Scheme.exists_integral_zariski_refinement_of_surjective_etale
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T06:14:20.25119+00:00
-- url     : https://prove2.me/theorems/dda2dc96-7619-46e0-93e1-26d4ec019a05
-- title:
--   Integral Zariski refinement of a surjective étale morphism
-- statement:
--   Let $U \to X$ be a surjective étale morphism with $X$ quasi-compact and quasi-separated. There is a surjective integral morphism $P \to X$ that factors Zariski locally through $U \to X$.
-- source:
--   Stacks Project, Lemma 37.45.7, https://stacks.math.columbia.edu/tag/09Z0.

import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Integral

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.exists_integral_zariski_refinement_of_surjective_etale {U X : Scheme.{u}} [SpectralSpace X]
    (f : U ⟶ X) [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ X), IsIntegralHom p ∧ Surjective p ∧
      ∀ x : P, ∃ (W : Scheme.{u}) (i : W ⟶ P), IsOpenImmersion i ∧ x ∈ Set.range i ∧
        ∃ g : W ⟶ U, g ≫ f = i ≫ p := by sorry
