-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitary_bornRecover_empty
-- name    : BookProof.ChapterContinuityUnitary.bornRecover_empty
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T19:37:13.385269+00:00
-- url     : https://prove2.me/theorems/af3ab93d-2ddb-4af9-9dbc-93723d1ce00c
-- title:
--   The Lean 4 theorem `bornRecover_empty` in the `ChapterContinuityUnitary` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `bornRecover_empty` in the `ChapterContinuityUnitary` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterContinuityUnitary.lean

-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornRecover_empty
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct

theorem BookProof.ChapterContinuityUnitary.bornRecover_empty (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ) :
    bornRecover v t psi ∅ = 0 := by sorry
