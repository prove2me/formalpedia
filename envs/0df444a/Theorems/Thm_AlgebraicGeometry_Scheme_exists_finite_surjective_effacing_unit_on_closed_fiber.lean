-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_finite_surjective_effacing_unit_on_closed_fiber
-- name    : AlgebraicGeometry.Scheme.exists_finite_surjective_effacing_unit_on_closed_fiber
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-24T23:59:03.837104+00:00
-- url     : https://prove2.me/theorems/52fbbbea-cb6b-4803-8b35-55dae9dca020
-- title:
--   A finite cover kills a class of a finite constant direct image
-- statement:
--   Let $Z\hookrightarrow X$ be a closed immersion into an affine scheme,
--           let $p:Y\to X$ be finite, and let $M$ be a finite abelian group. A positive-degree class of
--           $(p_*\underline M)|_Z$ is killed by the restriction to $Z$ of the direct image along $p$
--           of the unit for some finite surjective $a:Y'\to Y$.
-- source:
--   Stacks Project, Lemmas 59.55.3 and 59.80.9, https://stacks.math.columbia.edu/tag/09ZD.

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

theorem AlgebraicGeometry.Scheme.exists_finite_surjective_effacing_unit_on_closed_fiber
    {X Z Y : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (p : Y ⟶ X) (_ : IsFinite p) (M : AddCommGrpCat.{u}) (_ : Finite M) (q : ℕ)
    (x : ((pullbackSheaves i).obj ((pushforward p).obj
      ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M))).H (q + 1)) :
    ∃ (Y' : Scheme.{u}) (a : Y' ⟶ Y), IsFinite a ∧ Surjective a ∧
      Sheaf.H.map ((pullbackSheaves i).map ((pushforward p).map ((pullbackAdjunction a).unit.app
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj M)))) (q + 1) x = 0 := by sorry
