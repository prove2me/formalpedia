-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_formInner_conj_symm
-- name    : BookProof.YangMillsFriedrichs.formInner_conj_symm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T19:20:15.989733+00:00
-- url     : https://prove2.me/theorems/15edb15f-bc16-4e39-b7d7-1e1bd1d77c2b
-- title:
--   The Lean 4 theorem `formInner_conj_symm` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `formInner_conj_symm` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.formInner_conj_symm
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.formInner_conj_symm {H : D →ₗ[ℂ] F} (hsym : SymmetricOn D H) (x y : D) :
    (starRingEnd ℂ) (formInner H y x) = formInner H x y := by sorry
