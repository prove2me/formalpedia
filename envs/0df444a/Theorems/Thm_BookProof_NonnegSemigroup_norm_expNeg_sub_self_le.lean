-- Prove2me | Theorems.Thm_BookProof_NonnegSemigroup_norm_expNeg_sub_self_le
-- name    : BookProof.NonnegSemigroup.norm_expNeg_sub_self_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T14:35:54.804518+00:00
-- url     : https://prove2.me/theorems/e6ea4f7d-fd93-4a88-9696-cb08af6cf97c
-- title:
--   `BookProof.NonnegSemigroup.norm_expNeg_sub_self_le` (A : F →L[ℂ] F) (hA : 0 ≤ A) {t : ℝ} (ht : 0 ≤ t) (x : F) : ‖expNeg A t x - x‖ ≤ t * ‖A x‖
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegSemigroup`.
--
--   `BookProof.NonnegSemigroup.norm_expNeg_sub_self_le` (A : F →L[ℂ] F) (hA : 0 ≤ A) {t : ℝ} (ht : 0 ≤ t) (x : F) : ‖expNeg A t x - x‖ ≤ t * ‖A x‖
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegSemigroup.norm_expNeg_sub_self_le`.

-- Generated from ChapterNonnegSemigroup.lean — theorem BookProof.NonnegSemigroup.norm_expNeg_sub_self_le
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup



open BookProof.ClosureUniqueness
open Filter Topology NormedSpace
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.NonnegSemigroup.norm_expNeg_sub_self_le (A : F →L[ℂ] F) (hA : 0 ≤ A) {t : ℝ} (ht : 0 ≤ t) (x : F) :
    ‖expNeg A t x - x‖ ≤ t * ‖A x‖ := by sorry
