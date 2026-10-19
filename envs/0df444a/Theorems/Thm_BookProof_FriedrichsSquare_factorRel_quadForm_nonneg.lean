-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_factorRel_quadForm_nonneg
-- name    : BookProof.FriedrichsSquare.factorRel_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:41:25.902331+00:00
-- url     : https://prove2.me/theorems/f67c7b0c-5320-4547-a35c-972ff9139d44
-- title:
--   `BookProof.FriedrichsSquare.factorRel_quadForm_nonneg` {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) : 0 ≤ (inner ℂ p.1 p.2 : ℂ).re ∧ (inner ℂ p.1 p.2 : ℂ).im = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.factorRel_quadForm_nonneg` {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) : 0 ≤ (inner ℂ p.1 p.2 : ℂ).re ∧ (inner ℂ p.1 p.2 : ℂ).im = 0
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.factorRel_quadForm_nonneg`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.factorRel_quadForm_nonneg
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterClosureUniqueness
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.factorRel_quadForm_nonneg {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorRel A) :
    0 ≤ (inner ℂ p.1 p.2 : ℂ).re ∧ (inner ℂ p.1 p.2 : ℂ).im = 0 := by sorry
