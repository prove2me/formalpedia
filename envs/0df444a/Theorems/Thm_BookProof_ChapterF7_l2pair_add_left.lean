-- Prove2me | Theorems.Thm_BookProof_ChapterF7_l2pair_add_left
-- name    : BookProof.ChapterF7.l2pair_add_left
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T05:05:27.858277+00:00
-- url     : https://prove2.me/theorems/c0466c38-ecd1-4dbf-9fc1-384c53a6f6c0
-- title:
--   `BookProof.ChapterF7.l2pair_add_left` (f₁ f₂ g : 𝓢(ℝ, ℂ)) : l2pair (f₁ + f₂) g = l2pair f₁ g + l2pair f₂ g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.l2pair_add_left` (f₁ f₂ g : 𝓢(ℝ, ℂ)) : l2pair (f₁ + f₂) g = l2pair f₁ g + l2pair f₂ g
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.l2pair_add_left`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.l2pair_add_left
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.l2pair_add_left (f₁ f₂ g : 𝓢(ℝ, ℂ)) :
    l2pair (f₁ + f₂) g = l2pair f₁ g + l2pair f₂ g := by sorry
