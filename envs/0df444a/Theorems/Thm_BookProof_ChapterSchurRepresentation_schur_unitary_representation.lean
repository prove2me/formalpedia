-- Prove2me | Theorems.Thm_BookProof_ChapterSchurRepresentation_schur_unitary_representation
-- name    : BookProof.ChapterSchurRepresentation.schur_unitary_representation
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:03:16.839985+00:00
-- url     : https://prove2.me/theorems/55f33954-61fe-42c9-a04f-c35a08884df4
-- title:
--   `BookProof.ChapterSchurRepresentation.schur_unitary_representation` {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V)) (hirr : (repSystem U).IsIrreducible) {S : V →L[ℂ] V} (hcomm : ∀ g
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurRepresentation`.
--
--   `BookProof.ChapterSchurRepresentation.schur_unitary_representation` {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V)) (hirr : (repSystem U).IsIrreducible) {S : V →L[ℂ] V} (hcomm : ∀ g : G, S * uCLM (U g) = uCLM (U g) * S) : ∃ c : ℂ, S = c • (1 : V →L[ℂ] V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurRepresentation.schur_unitary_representation`.

-- Generated from ChapterSchurRepresentation.lean — theorem BookProof.ChapterSchurRepresentation.schur_unitary_representation
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

theorem BookProof.ChapterSchurRepresentation.schur_unitary_representation {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V))
    (hirr : (repSystem U).IsIrreducible) {S : V →L[ℂ] V}
    (hcomm : ∀ g : G, S * uCLM (U g) = uCLM (U g) * S) :
    ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by sorry
