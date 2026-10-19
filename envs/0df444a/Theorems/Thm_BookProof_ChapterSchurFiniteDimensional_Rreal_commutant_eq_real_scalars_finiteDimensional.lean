-- Prove2me | Theorems.Thm_BookProof_ChapterSchurFiniteDimensional_Rreal_commutant_eq_real_scalars_finiteDimensional
-- name    : BookProof.ChapterSchurFiniteDimensional.Rreal_commutant_eq_real_scalars_finiteDimensional
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:00:39.018369+00:00
-- url     : https://prove2.me/theorems/d9c1bc14-d3d9-499b-8c03-8667a8b96368
-- title:
--   `BookProof.ChapterSchurFiniteDimensional.Rreal_commutant_eq_real_scalars_finiteDimensional` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) {θ : An
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurFiniteDimensional`.
--
--   `BookProof.ChapterSchurFiniteDimensional.Rreal_commutant_eq_real_scalars_finiteDimensional` [FiniteDimensional ℂ V] [Nontrivial V] (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V} (hθ : IsConjugation M θ) (S : V →L[ℂ] V) : (M.Commutes S ∧ CommutesConj θ S) ↔ ∃ r : ℝ, S = ((r : ℂ)) • (1 : V →L[ℂ] V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurFiniteDimensional.Rreal_commutant_eq_real_scalars_finiteDimensional`.

-- Generated from ChapterSchurFiniteDimensional.lean — theorem BookProof.ChapterSchurFiniteDimensional.Rreal_commutant_eq_real_scalars_finiteDimensional
import Mathlib
import Definitions.Def_ChapterSchurFiniteDimensional
import Definitions.Def_ChapterA
import Definitions.Def_ChapterA1
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurFiniteDimensional


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurFiniteDimensional.Rreal_commutant_eq_real_scalars_finiteDimensional [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V} (hθ : IsConjugation M θ)
    (S : V →L[ℂ] V) :
    (M.Commutes S ∧ CommutesConj θ S) ↔ ∃ r : ℝ, S = ((r : ℂ)) • (1 : V →L[ℂ] V) := by sorry
