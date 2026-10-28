-- Prove2me | Theorems.Thm_BookProof_NonnegSemigroup_norm_semigroupS_sub_approxS_le
-- name    : BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T15:03:23.429917+00:00
-- url     : https://prove2.me/theorems/32edebf1-7da5-45af-90b6-0fa7877a0e85
-- title:
--   `BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) (m : ℕ) {t : ℝ} (ht :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegSemigroup`.
--
--   `BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : ‖semigroupS hT hsv ht h - approxS hT m t h‖ ≤ t * ‖k - yosidaAt hT m h‖
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le`.

-- Generated from ChapterNonnegSemigroup.lean — theorem BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterPositiveSquareRootUnique
import Definitions.Def_ChapterNonnegResolvent
import Definitions.Def_ChapterNonnegUnitaryGroup
import Mathlib
import Definitions.Def_ChapterNonnegSemigroup



open BookProof.ClosureUniqueness
open BookProof.NonnegResolvent
open BookProof.PositiveSquareRoot
open Filter Topology NormedSpace
open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {T : Submodule ℂ (F × F)}

theorem BookProof.NonnegSemigroup.norm_semigroupS_sub_approxS_le (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {h k : F} (hk : (h, k) ∈ T) (m : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖semigroupS hT hsv ht h - approxS hT m t h‖ ≤ t * ‖k - yosidaAt hT m h‖ := by sorry
