-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_opGraph_eq_clGraph_of_isClosureOf
-- name    : BookProof.ClosureUniqueness.opGraph_eq_clGraph_of_isClosureOf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:30.717047+00:00
-- url     : https://prove2.me/theorems/17e619ba-111b-4787-bdc1-8cc329039cd1
-- title:
--   `BookProof.ClosureUniqueness.opGraph_eq_clGraph_of_isClosureOf` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (h : IsClosureOf T A) : opGraph A = clGraph T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.opGraph_eq_clGraph_of_isClosureOf` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (h : IsClosureOf T A) : opGraph A = clGraph T
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.opGraph_eq_clGraph_of_isClosureOf`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.opGraph_eq_clGraph_of_isClosureOf
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.opGraph_eq_clGraph_of_isClosureOf {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F}
    (h : IsClosureOf T A) : opGraph A = clGraph T := by sorry
