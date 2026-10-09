-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_opGraph_clExt
-- name    : BookProof.ClosureUniqueness.opGraph_clExt
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T21:37:45.504442+00:00
-- url     : https://prove2.me/theorems/fe88c402-fa6d-4595-a256-55fcc5b20d25
-- title:
--   `BookProof.ClosureUniqueness.opGraph_clExt` (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) : opGraph (clExt T hdense hsym) = clGraph T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.opGraph_clExt` (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) : opGraph (clExt T hdense hsym) = clGraph T
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.opGraph_clExt`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.opGraph_clExt
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

theorem BookProof.ClosureUniqueness.opGraph_clExt (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) :
    opGraph (clExt T hdense hsym) = clGraph T := by sorry
