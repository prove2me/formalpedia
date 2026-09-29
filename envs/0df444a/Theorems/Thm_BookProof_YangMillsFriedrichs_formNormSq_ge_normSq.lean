-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formNormSq_ge_normSq
-- name    : BookProof.YangMillsFriedrichs.formNormSq_ge_normSq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:15:26.520791+00:00
-- url     : https://prove2.me/theorems/7742df4b-3c3e-4e87-9f41-c8c40f1c6225
-- title:
--   The Lean 4 theorem `formNormSq_ge_normSq` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formNormSq_ge_normSq` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formNormSq_ge_normSq
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formNormSq_ge_normSq {H : D →ₗ[ℂ] F} (hpos : ∀ x : D, 0 ≤ quadForm H x) (x : D) :
    ‖(x : F)‖ ^ 2 ≤ formNormSq H x := by sorry
