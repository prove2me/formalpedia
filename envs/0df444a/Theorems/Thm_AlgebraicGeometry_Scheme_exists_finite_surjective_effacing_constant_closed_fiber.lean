-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_surjective_effacing_constant_closed_fiber
-- name    : AlgebraicGeometry.Scheme.exists_finite_surjective_effacing_constant_closed_fiber
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-25T00:30:12.624508+00:00
-- url     : https://prove2.me/theorems/712dfbdf-bda5-4cb2-b556-f48531184f47
-- title:
--   Finite surjective effacement for constant coefficients on an affine closed subscheme
-- statement:
--   Given a closed subscheme $W\hookrightarrow Y$ of an affine
--       scheme, a finite abelian group $M$, and a positive-degree class in $H^*(W,\underline M)$,
--       there is a finite surjection $Y'\to Y$ on whose closed base change $W\times_Y Y'$ the class
--       vanishes. The cohomology restriction is expressed using the inverse-image unit along the
--       finite projection $W\times_Y Y'\to W$.
-- source:
--   Stacks Project, Lemma 59.80.9(2), https://stacks.math.columbia.edu/tag/09ZD.

import Definitions.Def_AlgebraicGeometry_EtalePullbackAcyclicResolution
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Mathlib.RingTheory.Henselian

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackAdjunction)

theorem AlgebraicGeometry.Scheme.exists_finite_surjective_effacing_constant_closed_fiber
    {Y W : Scheme.{u}} [IsAffine Y] (j : W ⟶ Y) [IsClosedImmersion j]
    (M : AddCommGrpCat.{u}) (_ : Finite M) (q : ℕ)
    (x : ((pullbackSheaves j).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M)).H (q + 1)) :
    ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y), IsFinite a ∧ Surjective a ∧
      Sheaf.H.map ((pullbackAdjunction (pullback.fst j a)).unit.app
        ((pullbackSheaves j).obj ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M)))
        (q + 1) x = 0 := by sorry
