-- Prove2me | Theorems.Thm_BookProof_ChapterLpRestrictSplit_restrictEmbed_add_restrictEmbed_compl
-- name    : BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:46:55.330989+00:00
-- url     : https://prove2.me/theorems/c3c38842-e995-4b06-aa5e-08ea3e859f78
-- title:
--   `BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl` {A : Set α} (hA : MeasurableSet A) (u : Lp ℂ 2 mu) : restrictEmbed hA (restrictProj A u) + restrictEmbed hA
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpRestrictSplit`.
--
--   `BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl` {A : Set α} (hA : MeasurableSet A) (u : Lp ℂ 2 mu) : restrictEmbed hA (restrictProj A u) + restrictEmbed hA.compl (restrictProj Aᶜ u) = u
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl`.

-- Generated from ChapterLpRestrictSplit.lean — theorem BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl
import Definitions.Def_ChapterLinftyMultiplication
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
open BookProof.ChapterLpRestrictSplit


noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

theorem BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl {A : Set α} (hA : MeasurableSet A)
    (u : Lp ℂ 2 mu) :
    restrictEmbed hA (restrictProj A u) + restrictEmbed hA.compl (restrictProj Aᶜ u) = u := by sorry
