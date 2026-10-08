-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeShiftExample_expectation_shift_invariant
-- name    : BookProof.ChapterGaugeShiftExample.expectation_shift_invariant
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T11:17:43.185661+00:00
-- url     : https://prove2.me/theorems/9062b932-22b6-40c9-b8a5-7cb6ccfb6033
-- title:
--   `BookProof.ChapterGaugeShiftExample.expectation_shift_invariant` {A : L2Z →L[ℂ] L2Z} (hA : ∀ m : ℤ, A * shiftOp m = shiftOp m * A) (m : ℤ) (f : L2Z) : ⟪shiftOp m f, A (shiftOp m f)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeShiftExample`.
--
--   `BookProof.ChapterGaugeShiftExample.expectation_shift_invariant` {A : L2Z →L[ℂ] L2Z} (hA : ∀ m : ℤ, A * shiftOp m = shiftOp m * A) (m : ℤ) (f : L2Z) : ⟪shiftOp m f, A (shiftOp m f)⟫_ℂ = ⟪f, A f⟫_ℂ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeShiftExample.expectation_shift_invariant`.

-- Generated from ChapterGaugeShiftExample.lean — theorem BookProof.ChapterGaugeShiftExample.expectation_shift_invariant
import Mathlib
import Definitions.Def_ChapterGaugeShiftExample
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterGaugeShiftExample


open scoped InnerProductSpace


open BookProof.ChapterContinuityUnitaryInfinite

theorem BookProof.ChapterGaugeShiftExample.expectation_shift_invariant {A : L2Z →L[ℂ] L2Z}
    (hA : ∀ m : ℤ, A * shiftOp m = shiftOp m * A) (m : ℤ) (f : L2Z) :
    ⟪shiftOp m f, A (shiftOp m f)⟫_ℂ = ⟪f, A f⟫_ℂ := by sorry
