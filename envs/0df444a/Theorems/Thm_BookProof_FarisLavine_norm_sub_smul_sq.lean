-- Prove2me | Theorems.Thm_BookProof_FarisLavine_norm_sub_smul_sq
-- name    : BookProof.FarisLavine.norm_sub_smul_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:15:13.242901+00:00
-- url     : https://prove2.me/theorems/3d8dbeb6-9cbf-4852-871a-cb30c820e056
-- title:
--   The Lean 4 theorem `norm_sub_smul_sq` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `norm_sub_smul_sq` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.norm_sub_smul_sq
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.norm_sub_smul_sq (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (d : ℝ) (x : D) :
    ‖H x - ((d : ℂ) * Complex.I) • (x : F)‖ ^ 2 = ‖H x‖ ^ 2 + d ^ 2 * ‖(x : F)‖ ^ 2 := by sorry
