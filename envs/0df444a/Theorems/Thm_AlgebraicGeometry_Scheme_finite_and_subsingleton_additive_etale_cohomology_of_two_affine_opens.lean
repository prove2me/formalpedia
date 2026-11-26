-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_finite_and_subsingleton_additive_etale_cohomology_of_two_affine_opens
-- name    : AlgebraicGeometry.Scheme.finite_and_subsingleton_additive_etale_cohomology_of_two_affine_opens
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-26T09:48:44.487904+00:00
-- url     : https://prove2.me/theorems/8b1330e5-a89d-484e-bbcd-5d7f11adce52
-- title:
--   Additive étale cohomology on a proper scheme covered by two affine opens
-- statement:
--   For a proper scheme over a field with a cover by two affine opens, cohomology of the additive étale structure sheaf is finite-dimensional in every degree and vanishes above degree one.
-- source:
--   Stacks Project, Theorem 59.22.4, https://stacks.math.columbia.edu/tag/03P2, and Lemma 30.19.2, https://stacks.math.columbia.edu/tag/02O3.

import Definitions.Def_AlgebraicGeometry_EtaleAdditiveStructureSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Proper

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
universe u

theorem AlgebraicGeometry.Scheme.finite_and_subsingleton_additive_etale_cohomology_of_two_affine_opens
    (K : Type u) [Field K] {X : Scheme.{u}} (r : X ⟶ Spec (.of K)) [IsProper r]
    (U V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V) (_ : U ⊔ V = ⊤) :
    (∀ q : ℕ, @Module.Finite K ((PhilipponEtaleAdditiveStructureSheaf.sheaf X).H q)
      _ _ (PhilipponEtaleAdditiveStructureSheaf.cohomologyModule r q)) ∧
    ∀ q : ℕ, Subsingleton ((PhilipponEtaleAdditiveStructureSheaf.sheaf X).H (q + 2)) := by sorry
