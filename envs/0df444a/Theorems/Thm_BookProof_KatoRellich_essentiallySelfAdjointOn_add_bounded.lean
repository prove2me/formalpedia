-- Prove2me | Theorems.Thm_BookProof_KatoRellich_essentiallySelfAdjointOn_add_bounded
-- name    : BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T22:49:46.77631+00:00
-- url     : https://prove2.me/theorems/4ada5d33-0a56-4749-8dd7-5b074967b130
-- title:
--   `BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded` [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (B : F →L[ℂ] F) (hB : ∀
-- statement:
--   Prove the following Lean 4 theorem from `ChapterKatoRellichDeficiency`.
--
--   `BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded` [CompleteSpace F] (H : D →ₗ[ℂ] F) (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (B : F →L[ℂ] F) (hB : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) : EssentiallySelfAdjointOn D (H + (B.toLinearMap ∘ₗ D.subtype))
--
--   Formalization note: Lean 4 identifier `BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded`.

-- Generated from ChapterKatoRellichDeficiency.lean — theorem BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterKatoRellichDeficiency
import Definitions.Def_ChapterFarisLavineCore



open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

theorem BookProof.KatoRellich.essentiallySelfAdjointOn_add_bounded [CompleteSpace F] (H : D →ₗ[ℂ] F)
    (hH : SymmetricOn D H) (hesa : EssentiallySelfAdjointOn D H) (B : F →L[ℂ] F)
    (hB : ∀ x y : F, (inner ℂ (B x) y : ℂ) = inner ℂ x (B y)) :
    EssentiallySelfAdjointOn D (H + (B.toLinearMap ∘ₗ D.subtype)) := by sorry
