-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_frDom_le_clDom
-- name    : BookProof.FriedrichsSquare.frDom_le_clDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:41:46.041755+00:00
-- url     : https://prove2.me/theorems/5678442b-c708-4a91-ac12-d32cad554dfa
-- title:
--   `BookProof.FriedrichsSquare.frDom_le_clDom` (A : D →ₗ[ℂ] F) : frDom A ≤ clDom A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.frDom_le_clDom` (A : D →ₗ[ℂ] F) : frDom A ≤ clDom A
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.frDom_le_clDom`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.frDom_le_clDom
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterClosureUniqueness
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.frDom_le_clDom (A : D →ₗ[ℂ] F) : frDom A ≤ clDom A := by sorry
