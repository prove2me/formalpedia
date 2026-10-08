-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_clExt_isClosureOf
-- name    : BookProof.ClosureUniqueness.clExt_isClosureOf
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:38:00.952743+00:00
-- url     : https://prove2.me/theorems/02309f39-0239-4c21-a903-b47985750d55
-- title:
--   `BookProof.ClosureUniqueness.clExt_isClosureOf` (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) : IsClosureOf T (clExt T hdense hsym)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.clExt_isClosureOf` (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) : IsClosureOf T (clExt T hdense hsym)
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.clExt_isClosureOf`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.clExt_isClosureOf
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

theorem BookProof.ClosureUniqueness.clExt_isClosureOf (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) :
    IsClosureOf T (clExt T hdense hsym) := by sorry
