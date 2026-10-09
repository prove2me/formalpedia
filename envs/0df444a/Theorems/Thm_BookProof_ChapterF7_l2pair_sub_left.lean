-- Prove2me | Theorems.Thm_BookProof_ChapterF7_l2pair_sub_left
-- name    : BookProof.ChapterF7.l2pair_sub_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T05:05:58.964982+00:00
-- url     : https://prove2.me/theorems/4f7c2e6b-16ef-4dce-9d38-642ccdebaf81
-- title:
--   `BookProof.ChapterF7.l2pair_sub_left` (f₁ f₂ g : 𝓢(ℝ, ℂ)) : l2pair (f₁ - f₂) g = l2pair f₁ g - l2pair f₂ g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterF7`.
--
--   `BookProof.ChapterF7.l2pair_sub_left` (f₁ f₂ g : 𝓢(ℝ, ℂ)) : l2pair (f₁ - f₂) g = l2pair f₁ g - l2pair f₂ g
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterF7.l2pair_sub_left`.

-- Generated from ChapterF7.lean — theorem BookProof.ChapterF7.l2pair_sub_left
import Mathlib
import Definitions.Def_ChapterF7
open BookProof.ChapterF7


open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

theorem BookProof.ChapterF7.l2pair_sub_left (f₁ f₂ g : 𝓢(ℝ, ℂ)) :
    l2pair (f₁ - f₂) g = l2pair f₁ g - l2pair f₂ g := by sorry
