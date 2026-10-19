-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitary_bornRecover_mono
-- name    : BookProof.ChapterContinuityUnitary.bornRecover_mono
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T19:37:29.521981+00:00
-- url     : https://prove2.me/theorems/1573ae6b-f7fd-42a8-a796-f492a9534bf8
-- title:
--   The Lean 4 theorem `bornRecover_mono` in the `ChapterContinuityUnitary` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `bornRecover_mono` in the `ChapterContinuityUnitary` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterContinuityUnitary.lean

-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornRecover_mono
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct

theorem BookProof.ChapterContinuityUnitary.bornRecover_mono (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ)
    {B C : Finset (ZMod N)} (h : B ⊆ C) :
    bornRecover v t psi B ≤ bornRecover v t psi C := by sorry
