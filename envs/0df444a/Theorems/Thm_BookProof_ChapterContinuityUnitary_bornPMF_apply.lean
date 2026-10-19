-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitary_bornPMF_apply
-- name    : BookProof.ChapterContinuityUnitary.bornPMF_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T19:37:06.042005+00:00
-- url     : https://prove2.me/theorems/ff9a1ccf-b227-40e7-a785-92ba1caead3a
-- title:
--   The Lean 4 theorem `bornPMF_apply` in the `ChapterContinuityUnitary` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `bornPMF_apply` in the `ChapterContinuityUnitary` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterContinuityUnitary.lean

-- Generated from ChapterContinuityUnitary.lean — theorem BookProof.ChapterContinuityUnitary.bornPMF_apply
import Mathlib
import Definitions.Def_ChapterContinuityUnitary
open BookProof.ChapterContinuityUnitary

variable {N : ℕ} [NeZero N]


open scoped BigOperators Matrix TensorProduct

theorem BookProof.ChapterContinuityUnitary.bornPMF_apply (v : ZMod N → ℝ) (t : ℝ) (psi : ZMod N → ℂ)
    (hpsi : ∑ z, ‖psi z‖ ^ 2 = 1) (z : ZMod N) :
    bornPMF v t psi hpsi z = ENNReal.ofReal (‖evolvedState v t psi z‖ ^ 2) := by sorry
