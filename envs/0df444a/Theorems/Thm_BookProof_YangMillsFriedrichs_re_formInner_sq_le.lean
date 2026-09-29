-- Prove2me | Theorems.Thm_BookProof_YangMillsFriedrichs_re_formInner_sq_le
-- name    : BookProof.YangMillsFriedrichs.re_formInner_sq_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-12T23:56:10.947993+00:00
-- url     : https://prove2.me/theorems/995af3be-201e-4636-a8a3-cf9da5cf6f63
-- title:
--   The Lean 4 theorem `re_formInner_sq_le` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `re_formInner_sq_le` in the `ChapterYangMillsFriedrichs` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterYangMillsFriedrichs.lean

-- Generated from ChapterYangMillsFriedrichs.lean — theorem BookProof.YangMillsFriedrichs.re_formInner_sq_le
import Mathlib
import Definitions.Def_ChapterYangMillsFriedrichs
open BookProof.YangMillsFriedrichs


















open BookProof.FarisLavine




variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.YangMillsFriedrichs.re_formInner_sq_le {H : D →ₗ[ℂ] F} (hsym : SymmetricOn D H)
    (hpos : ∀ x : D, 0 ≤ quadForm H x) (x y : D) :
    (formInner H x y).re ^ 2 ≤ formNormSq H x * formNormSq H y := by sorry
