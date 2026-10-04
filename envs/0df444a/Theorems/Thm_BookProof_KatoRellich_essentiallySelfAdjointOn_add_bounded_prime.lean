-- Prove2me | Theorems.Thm_BookProof_KatoRellich_essentiallySelfAdjointOn_add_bounded_prime
-- name    : BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded_prime
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-03T07:23:43.091435+00:00
-- url     : https://prove2.me/theorems/0cec59b0-c23c-44bb-a37b-3494313cf0a9
-- title:
--   The Lean 4 theorem `essentiallySelfAdjointOn_add_bounded_prime` in the `ChapterKatoRellichRelative` chapter of the timepiece formalization
-- statement:
--   The Lean 4 theorem `essentiallySelfAdjointOn_add_bounded'` in the `ChapterKatoRellichRelative` chapter of the timepiece formalization.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterKatoRellichRelative.lean

-- Generated from ChapterKatoRellichRelative.lean — theorem BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded'
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterKatoRellichRelative
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterA4

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}



open BookProof.FarisLavine

theorem BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded_prime [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (B : F →L[ℂ] F)
    (hB : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) :
    EssentiallySelfAdjointOn D (H + (B.toLinearMap ∘ₗ D.subtype)) := by sorry
