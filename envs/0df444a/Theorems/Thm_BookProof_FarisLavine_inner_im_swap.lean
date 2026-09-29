-- Prove2me | Theorems.Thm_BookProof_FarisLavine_inner_im_swap
-- name    : BookProof.FarisLavine.inner_im_swap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T18:18:20.60236+00:00
-- url     : https://prove2.me/theorems/07a536a8-7538-4d11-9cf4-e1762a59a6af
-- title:
--   The Lean 4 theorem `inner_im_swap` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_im_swap` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.inner_im_swap
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.inner_im_swap (a b : F) : (inner ℂ b a : ℂ).im = -(inner ℂ a b : ℂ).im := by sorry
