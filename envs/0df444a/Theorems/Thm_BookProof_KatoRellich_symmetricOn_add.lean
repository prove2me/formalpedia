-- Prove2me | Theorems.Thm_BookProof_KatoRellich_symmetricOn_add
-- name    : BookProof.KatoRellich.symmetricOn_add
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-09-18T01:21:31.937331+00:00
-- url     : https://prove2.me/theorems/73ac0fba-4754-48c5-8c24-3da24f6de788
-- title:
--   The Lean 4 theorem `symmetricOn_add` in the `ChapterKatoRellichRelative` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `symmetricOn_add` in the `ChapterKatoRellichRelative` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterKatoRellichRelative.lean

-- Generated from ChapterKatoRellichRelative.lean — theorem BookProof.KatoRellich.symmetricOn_add
import Mathlib
import Definitions.Def_ChapterKatoRellichRelative
import Definitions.Def_ChapterEsaClosureCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.KatoRellich.symmetricOn_add {H B : D →ₗ[ℂ] F} (hH : SymmetricOn D H) (hB : SymmetricOn D B) :
    SymmetricOn D (H + B) := by sorry
