-- Prove2me | Theorems.Thm_BookProof_ChapterF7_l2pair_sub_right
-- name    : BookProof.ChapterF7.l2pair_sub_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:06:19.212979+00:00
-- url     : https://prove2.me/theorems/e98479d7-6425-403c-b286-584981940588
-- title:
--   `BookProof.ChapterF7.l2pair_sub_right` (f g₁ g₂ : 𝓢(ℝ, ℂ)) : l2pair f (g₁ - g₂) = l2pair f g₁ - l2pair f g₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.l2pair_sub_right` (f g₁ g₂ : 𝓢(ℝ, ℂ)) : l2pair f (g₁ - g₂) = l2pair f g₁ - l2pair f g₂
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.l2pair_sub_right`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.l2pair_sub_right
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.l2pair_sub_right (f g₁ g₂ : 𝓢(ℝ, ℂ)) :
    l2pair f (g₁ - g₂) = l2pair f g₁ - l2pair f g₂ := by sorry
