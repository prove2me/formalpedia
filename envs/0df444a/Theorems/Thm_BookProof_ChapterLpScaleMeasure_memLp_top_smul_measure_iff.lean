-- Prove2me | Theorems.Thm_BookProof_ChapterLpScaleMeasure_memLp_top_smul_measure_iff
-- name    : BookProof.ChapterLpScaleMeasure.memLp_top_smul_measure_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:48:00.524511+00:00
-- url     : https://prove2.me/theorems/d384cb9e-040c-4599-871f-eaca383241ab
-- title:
--   `BookProof.ChapterLpScaleMeasure.memLp_top_smul_measure_iff` (hc0 : c ≠ 0) {f : α → ℂ} : MemLp f ⊤ (c • nu) ↔ MemLp f ⊤ nu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpScaleMeasure`.
--
--   `BookProof.ChapterLpScaleMeasure.memLp_top_smul_measure_iff` (hc0 : c ≠ 0) {f : α → ℂ} : MemLp f ⊤ (c • nu) ↔ MemLp f ⊤ nu
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpScaleMeasure.memLp_top_smul_measure_iff`.

-- Generated from ChapterLpScaleMeasure.lean — theorem BookProof.ChapterLpScaleMeasure.memLp_top_smul_measure_iff
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLpScaleMeasure
open BookProof.ChapterLpScaleMeasure


noncomputable section

open MeasureTheory ENNReal


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

theorem BookProof.ChapterLpScaleMeasure.memLp_top_smul_measure_iff (hc0 : c ≠ 0) {f : α → ℂ} :
    MemLp f ⊤ (c • nu) ↔ MemLp f ⊤ nu := by sorry
