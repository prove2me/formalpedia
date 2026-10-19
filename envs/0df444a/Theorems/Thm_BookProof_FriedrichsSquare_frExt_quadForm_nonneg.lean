-- Prove2me | Theorems.Thm_BookProof_FriedrichsSquare_frExt_quadForm_nonneg
-- name    : BookProof.FriedrichsSquare.frExt_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-17T00:41:42.970326+00:00
-- url     : https://prove2.me/theorems/80848d5e-d75c-43c7-8cee-2555af68c5ac
-- title:
--   `BookProof.FriedrichsSquare.frExt_quadForm_nonneg` (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) (x : frDom A) : 0 ≤ (inner ℂ (x : F) (frExt A hdense hsym x
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFriedrichsSquareFactorization`.
--
--   `BookProof.FriedrichsSquare.frExt_quadForm_nonneg` (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D A) (x : frDom A) : 0 ≤ (inner ℂ (x : F) (frExt A hdense hsym x) : ℂ).re ∧ (inner ℂ (x : F) (frExt A hdense hsym x) : ℂ).im = 0
--
--   Formalization note: Lean 4 identifier `BookProof.FriedrichsSquare.frExt_quadForm_nonneg`.

-- Generated from ChapterFriedrichsSquareFactorization.lean — theorem BookProof.FriedrichsSquare.frExt_quadForm_nonneg
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterClosureUniqueness
import Mathlib
import Definitions.Def_ChapterFriedrichsSquareFactorization
import Definitions.Def_ChapterFarisLavineCore
open BookProof.FriedrichsSquare



open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}

variable [CompleteSpace F]

theorem BookProof.FriedrichsSquare.frExt_quadForm_nonneg (A : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D A) (x : frDom A) :
    0 ≤ (inner ℂ (x : F) (frExt A hdense hsym x) : ℂ).re ∧
      (inner ℂ (x : F) (frExt A hdense hsym x) : ℂ).im = 0 := by sorry
