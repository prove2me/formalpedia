-- Prove2me | Theorems.Thm_BookProof_ChapterG_haarAverage_one
-- name    : BookProof.ChapterG.haarAverage_one
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T14:09:26.182343+00:00
-- url     : https://prove2.me/theorems/4040276f-dfd2-4d5c-a386-b56818b8d002
-- title:
--   `BookProof.ChapterG.haarAverage_one` : haarAverage (μG
-- statement:
--   Prove the following Lean 4 theorem from `ChapterG`.
--
--   `BookProof.ChapterG.haarAverage_one` : haarAverage (μG
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterG.haarAverage_one`.

-- Generated from ChapterG.lean — theorem BookProof.ChapterG.haarAverage_one
import Mathlib
import Definitions.Def_ChapterG
open BookProof.ChapterG


open scoped ComplexConjugate InnerProductSpace Matrix














open MeasureTheory










variable {G : Type*} [Group G] [MeasurableSpace G]
variable {μG : Measure G} [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
variable {X : Type*} [MulAction G X]

theorem BookProof.ChapterG.haarAverage_one : haarAverage (μG := μG) (X := X) (fun _ => 1) = fun _ => 1 := by sorry
