-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_not_isSelfAdjointExtension_clExt_of_deficiency
-- name    : BookProof.ClosureUniqueness.not_isSelfAdjointExtension_clExt_of_deficiency
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:47:18.706986+00:00
-- url     : https://prove2.me/theorems/46dcde4f-2461-4c70-a2b9-bd25276de1a9
-- title:
--   `BookProof.ClosureUniqueness.not_isSelfAdjointExtension_clExt_of_deficiency` (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) {w : F} (hw0 : w ≠ 0) (hw : ∀ v :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.not_isSelfAdjointExtension_clExt_of_deficiency` (T : D →ₗ[ℂ] F) (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) {w : F} (hw0 : w ≠ 0) (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = Complex.I * inner ℂ (v : F) w) : ¬ IsSelfAdjointExtension T (clExt T hdense hsym)
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.not_isSelfAdjointExtension_clExt_of_deficiency`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.not_isSelfAdjointExtension_clExt_of_deficiency
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

theorem BookProof.ClosureUniqueness.not_isSelfAdjointExtension_clExt_of_deficiency (T : D →ₗ[ℂ] F)
    (hdense : Dense (D : Set F)) (hsym : SymmetricOn D T) {w : F} (hw0 : w ≠ 0)
    (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = Complex.I * inner ℂ (v : F) w) :
    ¬ IsSelfAdjointExtension T (clExt T hdense hsym) := by sorry
