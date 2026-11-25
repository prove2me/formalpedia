-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_ind_bounded_finite_constant_models
-- name    : AlgebraicGeometry.Scheme.ind_bounded_finite_constant_models
-- status  : Open
-- author  : @tomasz
-- created : 2026-11-25T08:41:07.698129+00:00
-- url     : https://prove2.me/theorems/9f081fd5-95eb-59f0-ad4e-32302feb5c4b
-- title:
--   Annihilated étale sheaves are filtered colimits of bounded finite constant models
-- statement:
--   Let $X$ be an affine scheme and $F$ an abelian étale sheaf annihilated by a positive integer $N$. Then $F$ is the filtered colimit of sheaves $F_j$ admitting a monomorphism $F_j\hookrightarrow p_*\underline{M}$ for a finite and finitely presented morphism $p$ and a finite abelian group $M$ annihilated by $N$.
-- source:
--   Stacks Project, Lemmas 59.51.4, 59.73.2 and 59.74.4, https://stacks.math.columbia.edu/tag/03Q5.

import Definitions.Def_AlgebraicGeometry_EtaleCohomologyRestriction
import Mathlib.CategoryTheory.ObjectProperty.Ind

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves)
universe u

theorem AlgebraicGeometry.Scheme.ind_bounded_finite_constant_models
    (X : Scheme.{u}) [IsAffine X] (N : ℕ) (_ : N ≠ 0)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) (_ : N • 𝟙 F = 0) :
    ObjectProperty.ind.{u} (fun E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} =>
        ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : LocallyOfFinitePresentation p)
          (M : AddCommGrpCat.{u}) (_ : Finite M), N • 𝟙 M = 0 ∧
            ∃ m : E ⟶ (pushforward p).obj ((constantSheaf Y.smallEtaleTopology
              AddCommGrpCat.{u}).obj M), Mono m) F := by sorry
