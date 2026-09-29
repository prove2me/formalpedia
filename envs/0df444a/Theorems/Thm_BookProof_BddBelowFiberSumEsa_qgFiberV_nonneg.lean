-- Prove2me | Theorems.Thm_BookProof_BddBelowFiberSumEsa_qgFiberV_nonneg
-- name    : BookProof.BddBelowFiberSumEsa.qgFiberV_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T11:11:34.279064+00:00
-- url     : https://prove2.me/theorems/f1702658-20dd-4a75-bc9d-36972350c725
-- title:
--   The Lean 4 theorem `qgFiberV_nonneg` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `qgFiberV_nonneg` in the `ChapterBddBelowFiberSumEsa` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterBddBelowFiberSumEsa.lean

-- Generated from ChapterBddBelowFiberSumEsa.lean — theorem BookProof.BddBelowFiberSumEsa.qgFiberV_nonneg
import Mathlib
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.BddBelowFiberSumEsa











open MeasureTheory
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa

noncomputable section

variable {ι : Type*}

theorem BookProof.BddBelowFiberSumEsa.qgFiberV_nonneg {M alpha : ℝ} (halpha : 0 < alpha) {d : ℕ} (omega : Fin d → ℝ)
    (i : Option (Fin d)) (x : ℝ) : 0 ≤ qgFiberV M alpha omega i x := by sorry
