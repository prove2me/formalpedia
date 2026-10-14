-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_opGraph_le_of_extends
-- name    : BookProof.ClosureUniqueness.opGraph_le_of_extends
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:20.814808+00:00
-- url     : https://prove2.me/theorems/5de66004-fe25-4897-80e9-80f7205c0b36
-- title:
--   `BookProof.ClosureUniqueness.opGraph_le_of_extends` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (h : Extends T A) : opGraph T ≤ opGraph A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.opGraph_le_of_extends` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (h : Extends T A) : opGraph T ≤ opGraph A
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.opGraph_le_of_extends`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.opGraph_le_of_extends
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.opGraph_le_of_extends {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (h : Extends T A) :
    opGraph T ≤ opGraph A := by sorry
