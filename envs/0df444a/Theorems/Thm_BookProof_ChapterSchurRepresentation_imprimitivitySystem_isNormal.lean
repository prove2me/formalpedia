-- Prove2me | Theorems.Thm_BookProof_ChapterSchurRepresentation_imprimitivitySystem_isNormal
-- name    : BookProof.ChapterSchurRepresentation.imprimitivitySystem_isNormal
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:03:35.588984+00:00
-- url     : https://prove2.me/theorems/35589420-29a4-4596-a327-6e7398a998ec
-- title:
--   `BookProof.ChapterSchurRepresentation.imprimitivitySystem_isNormal` {G : Type*} [Group G] {X : Type*} (U : G →* (V ≃ₗᵢ[ℂ] V)) (pvm : Set X → (V →L[ℂ] V)) (hpvm : ∀ A : Set X, IsSel
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurRepresentation`.
--
--   `BookProof.ChapterSchurRepresentation.imprimitivitySystem_isNormal` {G : Type*} [Group G] {X : Type*} (U : G →* (V ≃ₗᵢ[ℂ] V)) (pvm : Set X → (V →L[ℂ] V)) (hpvm : ∀ A : Set X, IsSelfAdjoint (pvm A)) : (imprimitivitySystem U pvm).IsNormal
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurRepresentation.imprimitivitySystem_isNormal`.

-- Generated from ChapterSchurRepresentation.lean — theorem BookProof.ChapterSchurRepresentation.imprimitivitySystem_isNormal
import Definitions.Def_ChapterSchurIrreducible
import Mathlib
import Definitions.Def_ChapterSchurRepresentation
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA.System
open BookProof.ChapterSchurRepresentation


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA.System BookProof.ChapterSchurIrreducible

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurRepresentation.imprimitivitySystem_isNormal {G : Type*} [Group G] {X : Type*}
    (U : G →* (V ≃ₗᵢ[ℂ] V)) (pvm : Set X → (V →L[ℂ] V))
    (hpvm : ∀ A : Set X, IsSelfAdjoint (pvm A)) :
    (imprimitivitySystem U pvm).IsNormal := by sorry
