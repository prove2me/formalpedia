-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_selfAdjoint_commutant_scalar
-- name    : BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:02:03.718998+00:00
-- url     : https://prove2.me/theorems/807ecb4d-c390-4cdc-b71f-2e60ed7866dc
-- title:
--   `BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar` (M : System ℂ V) (hirr : M.IsIrreducible) {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.Commutes T) : ∃ c : ℝ,
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar` (M : System ℂ V) (hirr : M.IsIrreducible) {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.Commutes T) : ∃ c : ℝ, T = (c : ℂ) • (1 : V →L[ℂ] V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar (M : System ℂ V) (hirr : M.IsIrreducible)
    {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.Commutes T) :
    ∃ c : ℝ, T = (c : ℂ) • (1 : V →L[ℂ] V) := by sorry
