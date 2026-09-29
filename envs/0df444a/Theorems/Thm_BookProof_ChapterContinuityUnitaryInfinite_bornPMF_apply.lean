-- Prove2me | Theorems.Thm_BookProof_ChapterContinuityUnitaryInfinite_bornPMF_apply
-- name    : BookProof.ChapterContinuityUnitaryInfinite.bornPMF_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T04:07:48.056102+00:00
-- url     : https://prove2.me/theorems/8ca15fa7-5aab-4de3-bb5f-4bd54afdd5ce
-- title:
--   (v : LinfZ) (t : ℝ) (psi : L2Z) (hpsi : ‖psi‖ = 1) (z : ℤ) : bornPMF v t psi hpsi z = ENNReal.ofReal (‖((evolvedState v t psi : L2Z) : ℤ → ℂ) z‖ ^ 2)
-- statement:
--   Lean 4 theorem `BookProof.ChapterContinuityUnitaryInfinite.bornPMF_apply` (module `BookProof.ChapterContinuityUnitaryInfinite`), source chapter `BookProof/ChapterChapterContinuityUnitaryInfinite.lean`.
-- source:
--   https://github.com/leonardopedrio/timepiece/blob/61595bc/BookProof/ChapterChapterContinuityUnitaryInfinite.lean

-- Generated from ChapterContinuityUnitaryInfinite.lean — theorem BookProof.ChapterContinuityUnitaryInfinite.bornPMF_apply
import Mathlib
import Definitions.Def_ChapterContinuityUnitaryInfinite
open BookProof.ChapterContinuityUnitaryInfinite







open scoped ENNReal InnerProductSpace

theorem BookProof.ChapterContinuityUnitaryInfinite.bornPMF_apply (v : LinfZ) (t : ℝ) (psi : L2Z) (hpsi : ‖psi‖ = 1) (z : ℤ) :
    bornPMF v t psi hpsi z
      = ENNReal.ofReal (‖((evolvedState v t psi : L2Z) : ℤ → ℂ) z‖ ^ 2) := by sorry
