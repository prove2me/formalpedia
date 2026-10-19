-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_commutant_scalar_of_irreducible
-- name    : BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-17T01:02:17.06462+00:00
-- url     : https://prove2.me/theorems/87889848-3e75-4bd8-a9d0-1241aba48047
-- title:
--   `BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible` (M : System ℂ V) (hM : M.IsNormal) (hirr : M.IsIrreducible) {S : V →L[ℂ] V} (hcomm : M.Commutes S) : ∃ c : ℂ, S
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible` (M : System ℂ V) (hM : M.IsNormal) (hirr : M.IsIrreducible) {S : V →L[ℂ] V} (hcomm : M.Commutes S) : ∃ c : ℂ, S = c • (1 : V →L[ℂ] V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) {S : V →L[ℂ] V} (hcomm : M.Commutes S) :
    ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by sorry
