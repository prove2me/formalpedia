-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_etale_cover_lift_of_proper_closed_fiber
-- name    : AlgebraicGeometry.Scheme.exists_finite_etale_cover_lift_of_proper_closed_fiber
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T06:54:47.090547+00:00
-- url     : https://prove2.me/theorems/73237ab6-d6f0-4754-80c9-347aac9ee5dc
-- title:
--   Finite étale covers lift from a proper closed fiber
-- statement:
--   For a scheme proper over a henselian local ring, each finite étale cover of its closed fiber is isomorphic to the restriction of a finite étale cover of the scheme.
-- source:
--   Stacks Project, Lemma 58.9.1, https://stacks.math.columbia.edu/tag/0A48.

import Definitions.Def_AlgebraicGeometry_EtaleClosedFiberSections
import Mathlib.RingTheory.Henselian

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem AlgebraicGeometry.Scheme.exists_finite_etale_cover_lift_of_proper_closed_fiber
    (A : Type u) [CommRing A] [HenselianLocalRing A] {Y T : Scheme.{u}}
    (g : Y ⟶ Spec (.of A)) [IsProper g]
    (s : T ⟶ Spec (.of (IsLocalRing.ResidueField A))) (j : T ⟶ Y)
    (_ : IsPullback s j (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) g) (V : T.Etale) [IsFinite V.hom] :
    ∃ W : Y.Etale, IsFinite W.hom ∧ Nonempty ((PhilipponEtaleBaseChangeComparison.baseChange j).obj W ≅ V) := by sorry
