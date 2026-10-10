-- Prove2me | Theorems.Thm_BookProof_ChapterLpRestrictSplit_restrictEmbed_intertwines
-- name    : BookProof.ChapterLpRestrictSplit.restrictEmbed_intertwines
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:47:38.214843+00:00
-- url     : https://prove2.me/theorems/fb4290bf-3f54-4f7f-80ca-ea6acb2580c5
-- title:
--   `BookProof.ChapterLpRestrictSplit.restrictEmbed_intertwines` {A : Set α} (hA : MeasurableSet A) {g : α → ℂ} (hg : MemLp g ⊤ mu) (u : Lp ℂ 2 (mu.restrict A)) : restrictEmbed hA (mul
-- statement:
--   Prove the following Lean 4 theorem from `ChapterLpRestrictSplit`.
--
--   `BookProof.ChapterLpRestrictSplit.restrictEmbed_intertwines` {A : Set α} (hA : MeasurableSet A) {g : α → ℂ} (hg : MemLp g ⊤ mu) (u : Lp ℂ 2 (mu.restrict A)) : restrictEmbed hA (multOp g (hg.restrict A) u) = multOp g hg (restrictEmbed hA u)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterLpRestrictSplit.restrictEmbed_intertwines`.

-- Generated from ChapterLpRestrictSplit.lean — theorem BookProof.ChapterLpRestrictSplit.restrictEmbed_intertwines
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit


noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

theorem BookProof.ChapterLpRestrictSplit.restrictEmbed_intertwines {A : Set α} (hA : MeasurableSet A) {g : α → ℂ}
    (hg : MemLp g ⊤ mu) (u : Lp ℂ 2 (mu.restrict A)) :
    restrictEmbed hA (multOp g (hg.restrict A) u) = multOp g hg (restrictEmbed hA u) := by sorry
