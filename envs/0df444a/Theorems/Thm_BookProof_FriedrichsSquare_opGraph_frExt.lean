-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_opGraph_frExt
-- name    : BookProof.FriedrichsSquare.opGraph_frExt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:41:22.86937+00:00
-- url     : https://prove2.me/theorems/278e8268-db5e-457e-835e-d96b4a791f23
-- title:
--   `BookProof.FriedrichsSquare.opGraph_frExt` (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) : opGraph (frExt A hdense hsym) = factorRel A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.opGraph_frExt` (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) : opGraph (frExt A hdense hsym) = factorRel A
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.opGraph_frExt`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.opGraph_frExt
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

theorem BookProof.FriedrichsSquare.opGraph_frExt (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) :
    opGraph (frExt A hdense hsym) = factorRel A := by sorry
