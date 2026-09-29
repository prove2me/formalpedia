-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichsLimit_quadForm_top_nonneg_of_dense
-- name    : BookProof.YangMillsFriedrichsLimit.quadForm_top_nonneg_of_dense
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:19:24.62668+00:00
-- url     : https://prove2.me/theorems/0c2ce08d-7a27-47bf-b2c4-a24cd96daecb
-- title:
--   The Lean 4 theorem `quadForm_top_nonneg_of_dense` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `quadForm_top_nonneg_of_dense` in the `ChapterYangMillsFriedrichsLimit` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichsLimit.lean

-- Generated from ChapterYangMillsFriedrichsLimit.lean — theorem BookProof.YangMillsFriedrichsLimit.quadForm_top_nonneg_of_dense
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichsLimit
open BookProof.YangMillsFriedrichsLimit








open BookProof.FarisLavine BookProof.YangMillsFriedrichs



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.YangMillsFriedrichsLimit.quadForm_top_nonneg_of_dense {D : Submodule ℂ F} (A : F →L[ℂ] F)
    (hdense : Dense (D : Set F))
    (hpos : ∀ x : D, 0 ≤ (inner ℂ (x : F) (A (x : F)) : ℂ).re) :
    ∀ y : (⊤ : Submodule ℂ F), 0 ≤ quadForm (topRestrict A) y := by sorry
