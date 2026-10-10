-- Prove2me | Theorems.Thm_BookProof_ChapterLpScaleMeasure_scaleUnitary_intertwines
-- name    : BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:47:58.827073+00:00
-- url     : https://prove2.me/theorems/77e3cdfd-269e-4ddb-a0a1-5db23be98640
-- title:
--   `BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines` (hc0 : c ≠ 0) (hctop : c ≠ ⊤) {g : α → ℂ} (hg : MemLp g ⊤ (c • nu)) (u : Lp ℂ 2 (c • nu)) : (scaleUnitary hc0 hctop (mult
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpScaleMeasure`.
--
--   `BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines` (hc0 : c ≠ 0) (hctop : c ≠ ⊤) {g : α → ℂ} (hg : MemLp g ⊤ (c • nu)) (u : Lp ℂ 2 (c • nu)) : (scaleUnitary hc0 hctop (multOp g hg u) : α → ℂ) =ᵐ[nu] fun x => g x * (scaleUnitary (nu := nu) hc0 hctop u : α → ℂ) x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines`.

-- Generated from ChapterLpScaleMeasure.lean — theorem BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines
import Mathlib
import Definitions.Def_ChapterLpScaleMeasure
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpScaleMeasure


noncomputable section

open MeasureTheory ENNReal


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {nu : Measure α} {c : ENNReal}

theorem BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines (hc0 : c ≠ 0) (hctop : c ≠ ⊤) {g : α → ℂ}
    (hg : MemLp g ⊤ (c • nu)) (u : Lp ℂ 2 (c • nu)) :
    (scaleUnitary hc0 hctop (multOp g hg u) : α → ℂ)
      =ᵐ[nu] fun x => g x * (scaleUnitary (nu := nu) hc0 hctop u : α → ℂ) x := by sorry
