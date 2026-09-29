-- Prove2me | Theorems.Thm_BookProof_FarisLavine_commForm_eq
-- name    : BookProof.FarisLavine.commForm_eq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:22:33.180029+00:00
-- url     : https://prove2.me/theorems/975144ae-6178-4cd7-bc55-55e6da5ca7a8
-- title:
--   The Lean 4 theorem `commForm_eq` in the `ChapterFarisLavineCore` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `commForm_eq` in the `ChapterFarisLavineCore` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFarisLavineCore.lean

-- Generated from ChapterFarisLavineCore.lean — theorem BookProof.FarisLavine.commForm_eq
import Mathlib
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FarisLavine












variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FarisLavine.commForm_eq (H N : D →ₗ[ℂ] F) (x : D) :
    commForm H N x = -2 * (inner ℂ (H x) (N x) : ℂ).im := by sorry
