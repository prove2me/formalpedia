-- Prove2me | Theorems.Thm_BookProof_NonnegSemigroup_norm_semigroupS_apply_le
-- name    : BookProof.NonnegSemigroup.norm_semigroupS_apply_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T14:36:21.436616+00:00
-- url     : https://prove2.me/theorems/61a7d57c-3937-4434-b9d0-75f77556942c
-- title:
--   `BookProof.NonnegSemigroup.norm_semigroupS_apply_le` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) (x : F) : ‖semigroupS hT hsv ht x‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegSemigroup`.
--
--   `BookProof.NonnegSemigroup.norm_semigroupS_apply_le` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) (x : F) : ‖semigroupS hT hsv ht x‖ ≤ ‖x‖
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegSemigroup.norm_semigroupS_apply_le`.

-- Generated from ChapterNonnegSemigroup.lean — theorem BookProof.NonnegSemigroup.norm_semigroupS_apply_le
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

theorem BookProof.NonnegSemigroup.norm_semigroupS_apply_le (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    ‖semigroupS hT hsv ht x‖ ≤ ‖x‖ := by sorry
