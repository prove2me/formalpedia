-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitary_bornRecover_union
-- name    : BookProof.ChapterContinuityUnitary.bornRecover_union
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-30T11:51:24.691339+00:00
-- url     : https://prove2.me/theorems/c6c3a479-ab3b-4d78-877f-38574769b9c8
-- title:
--   The Lean 4 theorem `bornRecover_union` in the `ChapterContinuityUnitary` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `bornRecover_union` in the `ChapterContinuityUnitary` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterContinuityUnitary.lean

-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornRecover_union
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct

theorem BookProof.ChapterContinuityUnitary.bornRecover_union (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ)
    {B C : Finset (ZMod N)} (h : Disjoint B C) :
    bornRecover v t psi (B ∪ C) = bornRecover v t psi B + bornRecover v t psi C := by sorry
