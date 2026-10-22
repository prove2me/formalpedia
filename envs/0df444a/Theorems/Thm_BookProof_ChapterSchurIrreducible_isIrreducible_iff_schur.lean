-- Prove2me | Theorems.Thm_BookProof_ChapterSchurIrreducible_isIrreducible_iff_schur
-- name    : BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T01:02:59.102373+00:00
-- url     : https://prove2.me/theorems/9252403e-f545-447a-9250-6d502ff5eb84
-- title:
--   `BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur` (M : System ℂ V) (hM : M.IsNormal) : M.IsIrreducible ↔ ∀ S : V →L[ℂ] V, M.Commutes S → IsSelfAdjoint S → ∃ c : ℂ, S = c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSchurIrreducible`.
--
--   `BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur` (M : System ℂ V) (hM : M.IsNormal) : M.IsIrreducible ↔ ∀ S : V →L[ℂ] V, M.Commutes S → IsSelfAdjoint S → ∃ c : ℂ, S = c • (1 : V →L[ℂ] V)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur`.

-- Generated from ChapterSchurIrreducible.lean — theorem BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur
import Mathlib
import Definitions.Def_ChapterSchurIrreducible
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA
open BookProof.ChapterSchurIrreducible


open scoped ComplexConjugate InnerProductSpace


open BookProof.ChapterA BookProof.ChapterA

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur (M : System ℂ V) (hM : M.IsNormal) :
    M.IsIrreducible ↔
      ∀ S : V →L[ℂ] V, M.Commutes S → IsSelfAdjoint S → ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by sorry
