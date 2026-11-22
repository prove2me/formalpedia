-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_zariski_refinement_of_surjective_etale_spec
-- name    : AlgebraicGeometry.Scheme.exists_finite_zariski_refinement_of_surjective_etale_spec
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-21T06:32:23.461176+00:00
-- url     : https://prove2.me/theorems/e1b14c47-8def-4b2c-8aec-c3ec45e1cfa5
-- title:
--   Finite Zariski refinement of an étale surjection over a spectrum
-- statement:
--   Let $U \to \operatorname{Spec}(R)$ be a surjective étale morphism. There is a finite surjective morphism $P \to \operatorname{Spec}(R)$ that factors Zariski locally through $U\to\operatorname{Spec}(R)$.
-- source:
--   Stacks Project, Lemma 37.45.7, https://stacks.math.columbia.edu/tag/09Z0.

import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.exists_finite_zariski_refinement_of_surjective_etale_spec {R : CommRingCat.{u}} {U : Scheme.{u}}
    (f : U ⟶ Spec R) [Etale f] [Surjective f] :
    ∃ (P : Scheme.{u}) (p : P ⟶ Spec R), IsFinite p ∧ Surjective p ∧
      ∀ x : P, ∃ (W : Scheme.{u}) (i : W ⟶ P), IsOpenImmersion i ∧ x ∈ Set.range i ∧
        ∃ g : W ⟶ U, g ≫ f = i ≫ p := by sorry
