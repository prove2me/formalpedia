-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_contDiff_qgFiberV
-- name    : BookProof.BddBelowFiberSumEsa.contDiff_qgFiberV
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:10:48.217011+00:00
-- url     : https://prove2.me/theorems/2fe77c94-929d-4bd3-9be8-7c5d1730db70
-- title:
--   The Lean 4 theorem `contDiff_qgFiberV` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `contDiff_qgFiberV` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.contDiff_qgFiberV
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.BddBelowFiberSumEsa











open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.contDiff_qgFiberV (M alpha : ℝ) {d : ℕ} (omega : Fin d → ℝ) (i : Option (Fin d)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (qgFiberV M alpha omega i) := by sorry
