-- Prove2me | Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_stronglyMeasurable_symbol
-- name    : BookProof.ChapterLinftyMaximalAbelian.stronglyMeasurable_symbol
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T10:57:31.407455+00:00
-- url     : https://prove2.me/theorems/e6478696-36d9-4199-8c83-8f9c188e4c18
-- title:
--   `BookProof.ChapterLinftyMaximalAbelian.stronglyMeasurable_symbol` (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : StronglyMeasurable (symbol T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLinftyMaximalAbelian`.
--
--   `BookProof.ChapterLinftyMaximalAbelian.stronglyMeasurable_symbol` (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : StronglyMeasurable (symbol T)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLinftyMaximalAbelian.stronglyMeasurable_symbol`.

-- Generated from ChapterLinftyMaximalAbelian.lean — theorem BookProof.ChapterLinftyMaximalAbelian.stronglyMeasurable_symbol
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
open BookProof.ChapterLinftyMaximalAbelian


noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

theorem BookProof.ChapterLinftyMaximalAbelian.stronglyMeasurable_symbol (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) :
    StronglyMeasurable (symbol T) := by sorry
