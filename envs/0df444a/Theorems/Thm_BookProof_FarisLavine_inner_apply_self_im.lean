-- Prove2me | Theorems.Thm_BookProof_FarisLavine_inner_apply_self_im
-- name    : BookProof.FarisLavine.inner_apply_self_im
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:22:14.976409+00:00
-- url     : https://prove2.me/theorems/c035924e-b806-4e0f-a465-f16d8cef8df8
-- title:
--   The Lean 4 theorem `inner_apply_self_im` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `inner_apply_self_im` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.inner_apply_self_im
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.inner_apply_self_im (T : D →ₗ[ℂ] F) (hT : SymmetricOn D T) (x : D) :
    (inner ℂ (T x) (x : F) : ℂ).im = 0 := by sorry
