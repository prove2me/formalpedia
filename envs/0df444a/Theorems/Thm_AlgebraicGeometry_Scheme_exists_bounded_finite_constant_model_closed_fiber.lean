-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_exists_bounded_finite_constant_model_closed_fiber
-- name    : AlgebraicGeometry.Scheme.exists_bounded_finite_constant_model_closed_fiber
-- status  : Proved
-- author  : @tomasz
-- created : 2026-11-24T23:59:15.267209+00:00
-- url     : https://prove2.me/theorems/12f1320f-f825-48da-995e-cfa0d28e87c2
-- title:
--   Bounded finite constant models for classes on an affine closed fiber
-- statement:
--   Let $Z\hookrightarrow X$ be a closed immersion into an affine scheme and
--           let $F$ be an abelian étale sheaf annihilated by a positive integer $N$. Each positive-degree
--           class on $Z$ with coefficients in $F|_Z$ comes from some $F_0\to F$ for which $F_0$ embeds in
--           $p_*\underline M$ with $p$ finite and finitely presented and $M$ a finite abelian group
--           annihilated by $N$.
-- source:
--   Stacks Project, Lemmas 59.73.2, 59.51.4 and 59.74.4, https://stacks.math.columbia.edu/tag/09ZE.

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

theorem AlgebraicGeometry.Scheme.exists_bounded_finite_constant_model_closed_fiber
    {X Z : Scheme.{u}} [IsAffine X] (i : Z ⟶ X) [IsClosedImmersion i]
    (N : ℕ) (_ : N ≠ 0) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (_ : N • 𝟙 F = 0)
    (q : ℕ) (x : ((pullbackSheaves i).obj F).H (q + 1)) :
    ∃ (F₀ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (v : F₀ ⟶ F)
      (x₀ : ((pullbackSheaves i).obj F₀).H (q + 1)),
      Sheaf.H.map ((pullbackSheaves i).map v) (q + 1) x₀ = x ∧
        ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : LocallyOfFinitePresentation p)
          (M : AddCommGrpCat.{u}) (_ : Finite M), N • 𝟙 M = 0 ∧
            ∃ m : F₀ ⟶ (pushforward p).obj ((constantSheaf Y.smallEtaleTopology
              AddCommGrpCat.{u}).obj M), Mono m := by sorry
