-- Prove2me | Theorems.Thm_BookProof_NonnegSemigroup_norm_semigroupS_sub_self_le_of_mem
-- name    : BookProof.NonnegSemigroup.norm_semigroupS_sub_self_le_of_mem
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T15:03:03.626314+00:00
-- url     : https://prove2.me/theorems/988535d7-2a2c-4113-9956-c4c732421820
-- title:
--   `BookProof.NonnegSemigroup.norm_semigroupS_sub_self_le_of_mem` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) {t : ℝ} (ht : 0 ≤
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegSemigroup`.
--
--   `BookProof.NonnegSemigroup.norm_semigroupS_sub_self_le_of_mem` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) {t : ℝ} (ht : 0 ≤ t) : ‖semigroupS hT hsv ht h - h‖ ≤ t * ‖k‖
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegSemigroup.norm_semigroupS_sub_self_le_of_mem`.

-- Generated from ChapterNonnegSemigroup.lean — theorem BookProof.NonnegSemigroup.norm_semigroupS_sub_self_le_of_mem
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

theorem BookProof.NonnegSemigroup.norm_semigroupS_sub_self_le_of_mem (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) {t : ℝ} (ht : 0 ≤ t) :
    ‖semigroupS hT hsv ht h - h‖ ≤ t * ‖k‖ := by sorry
