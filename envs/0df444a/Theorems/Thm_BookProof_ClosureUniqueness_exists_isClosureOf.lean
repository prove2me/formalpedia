-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_exists_isClosureOf
-- name    : BookProof.ClosureUniqueness.exists_isClosureOf
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:38:10.975997+00:00
-- url     : https://prove2.me/theorems/018990c6-6c7d-4466-b5c9-b85b26297630
-- title:
--   `BookProof.ClosureUniqueness.exists_isClosureOf` (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) : ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsClosureOf T A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.exists_isClosureOf` (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) : ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsClosureOf T A
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.exists_isClosureOf`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.exists_isClosureOf
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

theorem BookProof.ClosureUniqueness.exists_isClosureOf (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F))
    (hsym : SymmetricOn D T) : ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsClosureOf T A := by sorry
