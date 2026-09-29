-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_re_formInner_swap
-- name    : BookProof.YangMillsFriedrichs.re_formInner_swap
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:15:08.646191+00:00
-- url     : https://prove2.me/theorems/21de152d-dcd7-423a-b87b-06fbd4ba6726
-- title:
--   The Lean 4 theorem `re_formInner_swap` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `re_formInner_swap` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.re_formInner_swap
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.re_formInner_swap {H : D →ₗ[ℂ] F} (hsym : SymmetricOn D H) (x y : D) :
    (formInner H y x).re = (formInner H x y).re := by sorry
