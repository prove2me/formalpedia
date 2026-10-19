-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_clGraph_le_adjGraph
-- name    : BookProof.FriedrichsSquare.clGraph_le_adjGraph
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:39:56.300358+00:00
-- url     : https://prove2.me/theorems/26feb697-8545-4f8b-ae8b-f3c738bb17a2
-- title:
--   `BookProof.FriedrichsSquare.clGraph_le_adjGraph` {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) : clGraph A ≤ adjGraph A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.clGraph_le_adjGraph` {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) : clGraph A ≤ adjGraph A
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.clGraph_le_adjGraph`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.clGraph_le_adjGraph
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

theorem BookProof.FriedrichsSquare.clGraph_le_adjGraph {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) :
    clGraph A ≤ adjGraph A := by sorry
