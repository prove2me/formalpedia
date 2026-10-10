-- Prove2me | Theorems.Thm_BookProof_ChapterLpScaleMeasure_scaleUnitary_coeFn
-- name    : BookProof.ChapterLpScaleMeasure.scaleUnitary_coeFn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:48:12.479856+00:00
-- url     : https://prove2.me/theorems/3430e45a-f96e-4efe-bb1a-a8a15a121fc7
-- title:
--   `BookProof.ChapterLpScaleMeasure.scaleUnitary_coeFn` (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (u : Lp ℂ 2 (c • nu)) : (scaleUnitary hc0 hctop u : α → ℂ) =ᵐ[nu] fun x => (scaleConst c : ℂ) * (
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpScaleMeasure`.
--
--   `BookProof.ChapterLpScaleMeasure.scaleUnitary_coeFn` (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (u : Lp ℂ 2 (c • nu)) : (scaleUnitary hc0 hctop u : α → ℂ) =ᵐ[nu] fun x => (scaleConst c : ℂ) * (u : α → ℂ) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpScaleMeasure.scaleUnitary_coeFn`.

-- Generated from ChapterLpScaleMeasure.lean — theorem BookProof.ChapterLpScaleMeasure.scaleUnitary_coeFn
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLpScaleMeasure
open BookProof.ChapterLpScaleMeasure


noncomputable section

open MeasureTheory ENNReal


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

theorem BookProof.ChapterLpScaleMeasure.scaleUnitary_coeFn (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (u : Lp ℂ 2 (c • nu)) :
    (scaleUnitary hc0 hctop u : α → ℂ)
      =ᵐ[nu] fun x => (scaleConst c : ℂ) * (u : α → ℂ) x := by sorry
