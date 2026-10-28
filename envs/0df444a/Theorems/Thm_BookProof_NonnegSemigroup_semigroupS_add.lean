-- Prove2me | Theorems.Thm_BookProof_NonnegSemigroup_semigroupS_add
-- name    : BookProof.NonnegSemigroup.semigroupS_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T14:35:00.336829+00:00
-- url     : https://prove2.me/theorems/eb99e39c-8a03-4ea2-bf65-353618efd5c8
-- title:
--   `BookProof.NonnegSemigroup.semigroupS_add` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : semigroupS hT hsv (add_nonne
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegSemigroup`.
--
--   `BookProof.NonnegSemigroup.semigroupS_add` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) : semigroupS hT hsv (add_nonneg hs ht) = semigroupS hT hsv hs * semigroupS hT hsv ht
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegSemigroup.semigroupS_add`.

-- Generated from ChapterNonnegSemigroup.lean — theorem BookProof.NonnegSemigroup.semigroupS_add
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

theorem BookProof.NonnegSemigroup.semigroupS_add (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    semigroupS hT hsv (add_nonneg hs ht) = semigroupS hT hsv hs * semigroupS hT hsv ht := by sorry
