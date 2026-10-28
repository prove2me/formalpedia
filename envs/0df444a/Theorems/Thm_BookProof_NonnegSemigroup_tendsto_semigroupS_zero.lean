-- Prove2me | Theorems.Thm_BookProof_NonnegSemigroup_tendsto_semigroupS_zero
-- name    : BookProof.NonnegSemigroup.tendsto_semigroupS_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-25T14:36:02.041434+00:00
-- url     : https://prove2.me/theorems/c0b6e227-98df-4e54-84d5-3f1706a9f0bc
-- title:
--   `BookProof.NonnegSemigroup.tendsto_semigroupS_zero` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : F) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ (t : ℝ) (ht : 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNonnegSemigroup`.
--
--   `BookProof.NonnegSemigroup.tendsto_semigroupS_zero` (hT : IsNonnegSelfAdjoint T) (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : F) {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ (t : ℝ) (ht : 0 ≤ t), t < δ → ‖semigroupS hT hsv ht x - x‖ < ε
--
--   Formalization note: Lean 4 identifier `BookProof.NonnegSemigroup.tendsto_semigroupS_zero`.

-- Generated from ChapterNonnegSemigroup.lean — theorem BookProof.NonnegSemigroup.tendsto_semigroupS_zero
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

theorem BookProof.NonnegSemigroup.tendsto_semigroupS_zero (hT : IsNonnegSelfAdjoint T)
    (hsv : ∀ w : F, ((0 : F), w) ∈ T → w = 0) (x : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ (t : ℝ) (ht : 0 ≤ t), t < δ → ‖semigroupS hT hsv ht x - x‖ < ε := by sorry
