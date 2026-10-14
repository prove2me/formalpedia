-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_compGraph_eq_of_isClosureOf
-- name    : BookProof.ClosureUniqueness.compGraph_eq_of_isClosureOf
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:52.795022+00:00
-- url     : https://prove2.me/theorems/259ab5d3-56ac-457b-acf9-cfe4f0339268
-- title:
--   `BookProof.ClosureUniqueness.compGraph_eq_of_isClosureOf` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsClosureOf T A) : compGraph A = factorGraph T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.compGraph_eq_of_isClosureOf` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsClosureOf T A) : compGraph A = factorGraph T
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.compGraph_eq_of_isClosureOf`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.compGraph_eq_of_isClosureOf
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.compGraph_eq_of_isClosureOf {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (hA : IsClosureOf T A) :
    compGraph A = factorGraph T := by sorry
