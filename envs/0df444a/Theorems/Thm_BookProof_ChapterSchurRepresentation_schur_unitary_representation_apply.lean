-- Prove2me | Theorems.Thm_BookProof_ChapterSchurRepresentation_schur_unitary_representation_apply
-- name    : BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:03:26.625989+00:00
-- url     : https://prove2.me/theorems/2e7d8a48-b76b-4445-a3ed-f8735e60d928
-- title:
--   `BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply` {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V)) (hirr : (repSystem U).IsIrreducible) {S : V →L[ℂ] V} (hcomm
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurRepresentation`.
--
--   `BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply` {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V)) (hirr : (repSystem U).IsIrreducible) {S : V →L[ℂ] V} (hcomm : ∀ (g : G) (x : V), S (U g x) = U g (S x)) : ∃ c : ℂ, ∀ x, S x = c • x
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply`.

-- Generated from ChapterSchurRepresentation.lean — theorem BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply
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

theorem BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply {G : Type*} [Group G] (U : G →* (V ≃ₗᵢ[ℂ] V))
    (hirr : (repSystem U).IsIrreducible) {S : V →L[ℂ] V}
    (hcomm : ∀ (g : G) (x : V), S (U g x) = U g (S x)) :
    ∃ c : ℂ, ∀ x, S x = c • x := by sorry
