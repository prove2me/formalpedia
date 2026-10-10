-- Prove2me | Theorems.Thm_BookProof_ChapterLpRestrictSplit_isHilbertSum_splitEmbed
-- name    : BookProof.ChapterLpRestrictSplit.isHilbertSum_splitEmbed
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:47:12.729833+00:00
-- url     : https://prove2.me/theorems/0f89b465-9954-4837-b987-e151e987ba25
-- title:
--   `BookProof.ChapterLpRestrictSplit.isHilbertSum_splitEmbed` {A : Set α} (hA : MeasurableSet A) : IsHilbertSum ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet A b))) (splitEmbed hA)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpRestrictSplit`.
--
--   `BookProof.ChapterLpRestrictSplit.isHilbertSum_splitEmbed` {A : Set α} (hA : MeasurableSet A) : IsHilbertSum ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet A b))) (splitEmbed hA)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpRestrictSplit.isHilbertSum_splitEmbed`.

-- Generated from ChapterLpRestrictSplit.lean — theorem BookProof.ChapterLpRestrictSplit.isHilbertSum_splitEmbed
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
open BookProof.ChapterLpRestrictSplit


noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

theorem BookProof.ChapterLpRestrictSplit.isHilbertSum_splitEmbed {A : Set α} (hA : MeasurableSet A) :
    IsHilbertSum ℂ (fun b : Bool => Lp ℂ 2 (mu.restrict (splitSet A b))) (splitEmbed hA) := by sorry
