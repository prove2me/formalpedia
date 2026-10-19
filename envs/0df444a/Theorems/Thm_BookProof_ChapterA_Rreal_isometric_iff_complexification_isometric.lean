-- Prove2me | Theorems.Thm_BookProof_ChapterA_Rreal_isometric_iff_complexification_isometric
-- name    : BookProof.ChapterA.Rreal_isometric_iff_complexification_isometric
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:19:19.346991+00:00
-- url     : https://prove2.me/theorems/59d14fe2-98b7-4e74-a305-116da85f942c
-- title:
--   `BookProof.ChapterA.Rreal_isometric_iff_complexification_isometric` (M : System ℂ V) (N : System ℂ W) (hN : IsSchurUnitary N) {θM : AntiUnitary V} {θN : AntiUnitary W} (hθM : IsCon
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA2d`.
--
--   `BookProof.ChapterA.Rreal_isometric_iff_complexification_isometric` (M : System ℂ V) (N : System ℂ W) (hN : IsSchurUnitary N) {θM : AntiUnitary V} {θN : AntiUnitary W} (hθM : IsConjugation M θM) (hθN : IsConjugation N θN) : (∃ α : V ≃ₗᵢ[ℂ] W, IsSystemIso M N α ∧ ∀ x, α (θM x) = θN (α x)) ↔ (∃ α : V ≃ₗᵢ[ℂ] W, IsSystemIso M N α)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.Rreal_isometric_iff_complexification_isometric`.

-- Generated from ChapterA2d.lean — theorem BookProof.ChapterA.Rreal_isometric_iff_complexification_isometric
import Mathlib
import Definitions.Def_ChapterA2d
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA


open scoped ComplexConjugate InnerProductSpace


variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

theorem BookProof.ChapterA.Rreal_isometric_iff_complexification_isometric
    (M : System ℂ V) (N : System ℂ W) (hN : IsSchurUnitary N)
    {θM : AntiUnitary V} {θN : AntiUnitary W}
    (hθM : IsConjugation M θM) (hθN : IsConjugation N θN) :
    (∃ α : V ≃ₗᵢ[ℂ] W, IsSystemIso M N α ∧ ∀ x, α (θM x) = θN (α x)) ↔
    (∃ α : V ≃ₗᵢ[ℂ] W, IsSystemIso M N α) := by sorry
