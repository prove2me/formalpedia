-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_commutant_eq_scalars_of_irreducible
-- name    : BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T01:21:56.608985+00:00
-- url     : https://prove2.me/theorems/0fbaa27b-90ce-41a2-91b1-5cd581a80b89
-- title:
--   `BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible` (M : System ℂ V) (hM : M.IsNormal) (hirr : M.IsIrreducible) (S : V →L[ℂ] V) : M.Commutes S ↔ ∃ c : ℂ, S = c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible` (M : System ℂ V) (hM : M.IsNormal) (hirr : M.IsIrreducible) (S : V →L[ℂ] V) : M.Commutes S ↔ ∃ c : ℂ, S = c • (1 : V →L[ℂ] V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) (S : V →L[ℂ] V) :
    M.Commutes S ↔ ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by sorry
