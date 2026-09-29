-- Prove2me | Theorems.Thm_BookProof_FarisLavine_quadForm_im
-- name    : BookProof.FarisLavine.quadForm_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:15:40.351978+00:00
-- url     : https://prove2.me/theorems/d0a0889b-5d7f-45c1-8d2d-24c29bfe18c0
-- title:
--   The Lean 4 theorem `quadForm_im` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadForm_im` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.quadForm_im
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.quadForm_im (N : D →ₗ[ℂ] F) (hN : SymmetricOn D N) (x : D) :
    (inner ℂ (x : F) (N x) : ℂ).im = 0 := by sorry
