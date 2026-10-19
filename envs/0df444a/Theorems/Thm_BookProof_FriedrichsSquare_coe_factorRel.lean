-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_coe_factorRel
-- name    : BookProof.FriedrichsSquare.coe_factorRel
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:39:44.769575+00:00
-- url     : https://prove2.me/theorems/ea2ed48d-e4ad-41ce-b488-c7b5efaf05fb
-- title:
--   `BookProof.FriedrichsSquare.coe_factorRel` (A : D →ₗ[ℂ] F) : (factorRel A : Set (F × F)) = factorGraph A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.coe_factorRel` (A : D →ₗ[ℂ] F) : (factorRel A : Set (F × F)) = factorGraph A
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.coe_factorRel`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.coe_factorRel
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

theorem BookProof.FriedrichsSquare.coe_factorRel (A : D →ₗ[ℂ] F) : (factorRel A : Set (F × F)) = factorGraph A := by sorry
