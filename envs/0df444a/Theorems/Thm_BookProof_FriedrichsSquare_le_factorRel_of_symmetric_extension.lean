-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_le_factorRel_of_symmetric_extension
-- name    : BookProof.FriedrichsSquare.le_factorRel_of_symmetric_extension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:41:11.834988+00:00
-- url     : https://prove2.me/theorems/e8c8184a-8647-426b-a5bf-8a02cee3a089
-- title:
--   `BookProof.FriedrichsSquare.le_factorRel_of_symmetric_extension` {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R : Submodule ℂ (F × F)} (hext : ∀ v : D
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.le_factorRel_of_symmetric_extension` {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A) {hstab : ∀ v : D, (A v : F) ∈ D} {R : Submodule ℂ (F × F)} (hext : ∀ v : D, ((v : F), sqOp A hstab v) ∈ R) (hRsym : ∀ p ∈ R, ∀ q ∈ R, (inner ℂ p.2 q.1 : ℂ) = inner ℂ p.1 q.2) (hdom : ∀ p ∈ R, p.1 ∈ clDom A) : R ≤ factorRel A
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.le_factorRel_of_symmetric_extension`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.le_factorRel_of_symmetric_extension
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

theorem BookProof.FriedrichsSquare.le_factorRel_of_symmetric_extension {A : D →ₗ[ℂ] F} (hsym : SymmetricOn D A)
    {hstab : ∀ v : D, (A v : F) ∈ D} {R : Submodule ℂ (F × F)}
    (hext : ∀ v : D, ((v : F), sqOp A hstab v) ∈ R)
    (hRsym : ∀ p ∈ R, ∀ q ∈ R, (inner ℂ p.2 q.1 : ℂ) = inner ℂ p.1 q.2)
    (hdom : ∀ p ∈ R, p.1 ∈ clDom A) : R ≤ factorRel A := by sorry
