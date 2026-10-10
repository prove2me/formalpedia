-- Prove2me | Theorems.Thm_BookProof_InverseTransform_seedSet_measure
-- name    : BookProof.InverseTransform.seedSet_measure
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:17:09.579106+00:00
-- url     : https://prove2.me/theorems/81ae051a-7935-4ccd-b396-0052f04469c7
-- title:
--   `BookProof.InverseTransform.seedSet_measure` (k : ℕ) : volume (seedSet p k) = ENNReal.ofReal (p k)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterInverseTransform`.
--
--   `BookProof.InverseTransform.seedSet_measure` (k : ℕ) : volume (seedSet p k) = ENNReal.ofReal (p k)
--
--   Formalization note: Lean 4 identifier `BookProof.InverseTransform.seedSet_measure`.

-- Generated from ChapterInverseTransform.lean — theorem BookProof.InverseTransform.seedSet_measure
import Mathlib
import Definitions.Def_ChapterInverseTransform
open BookProof.InverseTransform



open MeasureTheory Set Function

variable {n : ℕ} (p : ℕ → ℝ)

theorem BookProof.InverseTransform.seedSet_measure (k : ℕ) :
    volume (seedSet p k) = ENNReal.ofReal (p k) := by sorry
