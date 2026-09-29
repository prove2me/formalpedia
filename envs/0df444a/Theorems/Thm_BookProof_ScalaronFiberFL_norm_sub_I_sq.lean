-- Prove2me | Theorems.Thm_BookProof_ScalaronFiberFL_norm_sub_I_sq
-- name    : BookProof.ScalaronFiberFL.norm_sub_I_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-17T19:43:07.968872+00:00
-- url     : https://prove2.me/theorems/21d5e63f-1216-4b6d-9c26-e3c161dae2d0
-- title:
--   The Lean 4 theorem `norm_sub_I_sq` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sub_I_sq` in the `ChapterScalaronFiberFL` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterScalaronFiberFL.lean

-- Generated from ChapterScalaronFiberFL.lean — theorem BookProof.ScalaronFiberFL.norm_sub_I_sq
import Mathlib
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem BookProof.ScalaronFiberFL.norm_sub_I_sq {D : Submodule ℂ F} (N : D →ₗ[ℂ] F)
    (hsym : SymmetricOn D N) (u : D) :
    ‖N u - Complex.I • (u : F)‖ ^ 2 = ‖N u‖ ^ 2 + ‖(u : F)‖ ^ 2 := by sorry
