-- Prove2me | Theorems.Thm_BookProof_ChapterSirkEndToEnd_tendsto_zero_of_le_sirkBound
-- name    : BookProof.ChapterSirkEndToEnd.tendsto_zero_of_le_sirkBound
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-10T00:48:12.884249+00:00
-- url     : https://prove2.me/theorems/7e67880a-4283-460b-bc73-c39594358682
-- title:
--   (err : ℕ → ℝ) (C Dmin h nv : ℝ) (hh : 0 < h) (hnn : ∀ m, 0 ≤ err m) (hle : ∀ m, err m ≤ sirkBound C Dmin h nv m) : Tendsto err atTop (𝓝 0)
-- statement:
--   Lean 4 theorem `BookProof.ChapterSirkEndToEnd.tendsto_zero_of_le_sirkBound` (module `BookProof.ChapterSirkEndToEnd`), source chapter `BookProof/ChapterChapterSirkEndToEnd.lean`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterChapterSirkEndToEnd.lean

-- Generated from ChapterSirkEndToEnd.lean — theorem BookProof.ChapterSirkEndToEnd.tendsto_zero_of_le_sirkBound
import Mathlib
import Definitions.Def_ChapterSirkEndToEnd
open BookProof.ChapterSirkEndToEnd










noncomputable section

open Filter Topology


open BookProof.ChapterH4 BookProof.ChapterH6 BookProof.ChapterH8 BookProof.ChapterH9

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ChapterSirkEndToEnd.tendsto_zero_of_le_sirkBound (err : ℕ → ℝ) (C Dmin h nv : ℝ) (hh : 0 < h)
    (hnn : ∀ m, 0 ≤ err m) (hle : ∀ m, err m ≤ sirkBound C Dmin h nv m) :
    Tendsto err atTop (𝓝 0) := by sorry
