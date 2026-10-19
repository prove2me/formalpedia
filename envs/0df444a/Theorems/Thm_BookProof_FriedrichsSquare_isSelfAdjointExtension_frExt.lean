-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_isSelfAdjointExtension_frExt
-- name    : BookProof.FriedrichsSquare.isSelfAdjointExtension_frExt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:41:41.588304+00:00
-- url     : https://prove2.me/theorems/064ba226-2f36-4dc8-9b8d-edb4fcaccf8e
-- title:
--   `BookProof.FriedrichsSquare.isSelfAdjointExtension_frExt` [CompleteSpace F] (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) (hstab : ∀ v : D, (A v : F) ∈ D) :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.isSelfAdjointExtension_frExt` [CompleteSpace F] (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) (hstab : ∀ v : D, (A v : F) ∈ D) : IsSelfAdjointExtension (sqOp A hstab) (frExt A hdense hsym)
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.isSelfAdjointExtension_frExt`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.isSelfAdjointExtension_frExt
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.ClosureUniqueness
open BookProof.EsaClosure
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.isSelfAdjointExtension_frExt [CompleteSpace F] (A : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) (hstab : ∀ v : D, (A v : F) ∈ D) :
    IsSelfAdjointExtension (sqOp A hstab) (frExt A hdense hsym) := by sorry
