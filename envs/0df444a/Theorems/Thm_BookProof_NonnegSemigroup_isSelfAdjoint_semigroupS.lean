-- Prove2me | Theorems.Thm_BookProof_NonnegSemigroup_isSelfAdjoint_semigroupS
-- name    : BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T14:35:44.284268+00:00
-- url     : https://prove2.me/theorems/365545e9-5133-4836-bf58-1e061491b775
-- title:
--   `BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) : IsSelfAdjoint (semigroupS hT hsv
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegSemigroup`.
--
--   `BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) : IsSelfAdjoint (semigroupS hT hsv ht)
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS`.

-- Generated from ChapterNonnegSemigroup.lean — theorem BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup



open BookProof.ClosureUniqueness
open BookProof.PositiveSquareRoot
open Filter Topology NormedSpace
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {T : Submodule ℂ (F × F)}

theorem BookProof.NonnegSemigroup.isSelfAdjoint_semigroupS (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) :
    IsSelfAdjoint (semigroupS hT hsv ht) := by sorry
