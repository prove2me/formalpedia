-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitary_bornRecover_nonneg
-- name    : BookProof.ChapterContinuityUnitary.bornRecover_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T19:37:35.059517+00:00
-- url     : https://prove2.me/theorems/1b5e9320-58aa-42ca-9f01-c59d7ca4b062
-- title:
--   The Lean 4 theorem `bornRecover_nonneg` in the `ChapterContinuityUnitary` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `bornRecover_nonneg` in the `ChapterContinuityUnitary` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterContinuityUnitary.lean

-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornRecover_nonneg
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct

theorem BookProof.ChapterContinuityUnitary.bornRecover_nonneg (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ)
    (B : Finset (ZMod N)) : 0 ≤ bornRecover v t psi B := by sorry
