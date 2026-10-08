-- Prove2me | Theorems.Thm_BookProof_ChapterF7_l2pair_add_right
-- name    : BookProof.ChapterF7.l2pair_add_right
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:04:57.549528+00:00
-- url     : https://prove2.me/theorems/1a600015-1eb6-454b-8cc8-75e265306aeb
-- title:
--   `BookProof.ChapterF7.l2pair_add_right` (f g₁ g₂ : 𝓢(ℝ, ℂ)) : l2pair f (g₁ + g₂) = l2pair f g₁ + l2pair f g₂
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.l2pair_add_right` (f g₁ g₂ : 𝓢(ℝ, ℂ)) : l2pair f (g₁ + g₂) = l2pair f g₁ + l2pair f g₂
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.l2pair_add_right`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.l2pair_add_right
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.l2pair_add_right (f g₁ g₂ : 𝓢(ℝ, ℂ)) :
    l2pair f (g₁ + g₂) = l2pair f g₁ + l2pair f g₂ := by sorry
