-- Prove2me | Theorems.Thm_BookProof_ChapterSchurRepresentation_schur_imprimitivity
-- name    : BookProof.ChapterSchurRepresentation.schur_imprimitivity
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:03:58.795223+00:00
-- url     : https://prove2.me/theorems/318f676c-05d1-451c-8f41-7a33bb740583
-- title:
--   `BookProof.ChapterSchurRepresentation.schur_imprimitivity` {G : Type*} [Group G] {X : Type*} (U : G →* (V ≃ₗᵢ[ℂ] V)) (pvm : Set X → (V →L[ℂ] V)) (hpvm : ∀ A : Set X, IsSelfAdjoint
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurRepresentation`.
--
--   `BookProof.ChapterSchurRepresentation.schur_imprimitivity` {G : Type*} [Group G] {X : Type*} (U : G →* (V ≃ₗᵢ[ℂ] V)) (pvm : Set X → (V →L[ℂ] V)) (hpvm : ∀ A : Set X, IsSelfAdjoint (pvm A)) (hirr : (imprimitivitySystem U pvm).IsIrreducible) {S : V →L[ℂ] V} (hU : ∀ g : G, S * uCLM (U g) = uCLM (U g) * S) (hP : ∀ A : Set X, S * pvm A = pvm A * S) : ∃ c : ℂ, S = c • (1 : V →L[ℂ] V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurRepresentation.schur_imprimitivity`.

-- Generated from ChapterSchurRepresentation.lean — theorem BookProof.ChapterSchurRepresentation.schur_imprimitivity
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

theorem BookProof.ChapterSchurRepresentation.schur_imprimitivity {G : Type*} [Group G] {X : Type*}
    (U : G →* (V ≃ₗᵢ[ℂ] V)) (pvm : Set X → (V →L[ℂ] V))
    (hpvm : ∀ A : Set X, IsSelfAdjoint (pvm A))
    (hirr : (imprimitivitySystem U pvm).IsIrreducible) {S : V →L[ℂ] V}
    (hU : ∀ g : G, S * uCLM (U g) = uCLM (U g) * S)
    (hP : ∀ A : Set X, S * pvm A = pvm A * S) :
    ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by sorry
