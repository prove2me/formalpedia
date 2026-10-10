-- Prove2me | Theorems.Thm_BookProof_ChapterLpRestrictSplit_orthogonalFamily_splitEmbed
-- name    : BookProof.ChapterLpRestrictSplit.orthogonalFamily_splitEmbed
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:47:32.119717+00:00
-- url     : https://prove2.me/theorems/de99c44d-3057-4ef3-9665-72ad3ff3e736
-- title:
--   `BookProof.ChapterLpRestrictSplit.orthogonalFamily_splitEmbed` {A : Set α} (hA : MeasurableSet A) : OrthogonalFamily ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet A b))) (splitE
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpRestrictSplit`.
--
--   `BookProof.ChapterLpRestrictSplit.orthogonalFamily_splitEmbed` {A : Set α} (hA : MeasurableSet A) : OrthogonalFamily ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet A b))) (splitEmbed hA)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpRestrictSplit.orthogonalFamily_splitEmbed`.

-- Generated from ChapterLpRestrictSplit.lean — theorem BookProof.ChapterLpRestrictSplit.orthogonalFamily_splitEmbed
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
open BookProof.ChapterLpRestrictSplit


noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

theorem BookProof.ChapterLpRestrictSplit.orthogonalFamily_splitEmbed {A : Set α} (hA : MeasurableSet A) :
    OrthogonalFamily ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet A b)))
      (splitEmbed hA) := by sorry
