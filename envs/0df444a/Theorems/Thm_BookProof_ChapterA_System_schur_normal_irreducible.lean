-- Prove2me | Theorems.Thm_BookProof_ChapterA_System_schur_normal_irreducible
-- name    : BookProof.ChapterA.System.schur_normal_irreducible
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-06T04:24:54.377993+00:00
-- url     : https://prove2.me/theorems/4903f5fe-b495-4519-9a14-3686ce1ac6b6
-- title:
--   `BookProof.ChapterA.System.schur_normal_irreducible` (M : System 𝔽 V) (hM : IsNormal M) (hSchur : ∀ S : V →L[𝔽] V, M.Commutes S → IsSelfAdjoint S → ∃ c : 𝔽, S = c • (1 : V...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterA`.
--
--   `BookProof.ChapterA.System.schur_normal_irreducible` (M : System 𝔽 V) (hM : IsNormal M) (hSchur : ∀ S : V →L[𝔽] V, M.Commutes S → IsSelfAdjoint S → ∃ c : 𝔽, S = c • (1 : V →L[𝔽] V)) : IsIrreducible M
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterA.System.schur_normal_irreducible`.

-- Generated from ChapterA.lean — theorem BookProof.ChapterA.System.schur_normal_irreducible
import Mathlib
import Definitions.Def_ChapterA
open BookProof.ChapterA
open BookProof.ChapterA

variable {𝔽 : Type*} [RCLike 𝔽] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace 𝔽 V] [CompleteSpace V]


open scoped ComplexConjugate InnerProductSpace

theorem BookProof.ChapterA.System.schur_normal_irreducible (M : System 𝔽 V) (hM : IsNormal M)
    (hSchur : ∀ S : V →L[𝔽] V, M.Commutes S → IsSelfAdjoint S →
      ∃ c : 𝔽, S = c • (1 : V →L[𝔽] V)) :
    IsIrreducible M := by sorry
