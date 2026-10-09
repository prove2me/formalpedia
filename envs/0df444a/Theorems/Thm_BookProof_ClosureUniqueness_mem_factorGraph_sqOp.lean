-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_mem_factorGraph_sqOp
-- name    : BookProof.ClosureUniqueness.mem_factorGraph_sqOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:43:09.362204+00:00
-- url     : https://prove2.me/theorems/c15a8306-7d7b-4c81-ac6f-cbe5e4fb9adc
-- title:
--   `BookProof.ClosureUniqueness.mem_factorGraph_sqOp` (A : D →ₗ[ℂ] F) (hsym : SymmetricOn D A) (hstab : ∀ v : D, (A v : F) ∈ D) (v : D) : ((v : F), sqOp A hstab v) ∈ factorGraph A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.mem_factorGraph_sqOp` (A : D →ₗ[ℂ] F) (hsym : SymmetricOn D A) (hstab : ∀ v : D, (A v : F) ∈ D) (v : D) : ((v : F), sqOp A hstab v) ∈ factorGraph A
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.mem_factorGraph_sqOp`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.mem_factorGraph_sqOp
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.mem_factorGraph_sqOp (A : D →ₗ[ℂ] F) (hsym : SymmetricOn D A)
    (hstab : ∀ v : D, (A v : F) ∈ D) (v : D) :
    ((v : F), sqOp A hstab v) ∈ factorGraph A := by sorry
