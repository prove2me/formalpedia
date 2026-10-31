-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitary_tensorIsom_tmul
-- name    : BookProof.ChapterContinuityUnitary.tensorIsom_tmul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T12:05:50.487617+00:00
-- url     : https://prove2.me/theorems/3c9c55ca-e9e0-4490-9871-c9331ecb8917
-- title:
--   The Lean 4 theorem `tensorIsom_tmul` in the `ChapterContinuityUnitary` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `tensorIsom_tmul` in the `ChapterContinuityUnitary` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterContinuityUnitary.lean

-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.tensorIsom_tmul
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]
variable {X : Type*}


open scoped BigOperators Matrix TensorProduct

theorem BookProof.ChapterContinuityUnitary.tensorIsom_tmul (X Z : Type*) [Fintype Z] [DecidableEq Z]
    (f : X → ℂ) (g : Z → ℂ) :
    tensorIsom X Z (f ⊗ₜ g) = fun p => f p.1 * g p.2 := by sorry
