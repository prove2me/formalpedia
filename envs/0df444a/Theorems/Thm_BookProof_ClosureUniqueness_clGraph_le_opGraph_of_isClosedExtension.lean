-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_clGraph_le_opGraph_of_isClosedExtension
-- name    : BookProof.ClosureUniqueness.clGraph_le_opGraph_of_isClosedExtension
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:28.460979+00:00
-- url     : https://prove2.me/theorems/2e475664-7e71-4071-8bcf-9b554b17d0b1
-- title:
--   `BookProof.ClosureUniqueness.clGraph_le_opGraph_of_isClosedExtension` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (h : IsClosedExtension T A) : clGraph T ≤ opGraph A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.clGraph_le_opGraph_of_isClosedExtension` {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F} (h : IsClosedExtension T A) : clGraph T ≤ opGraph A
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.clGraph_le_opGraph_of_isClosedExtension`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.clGraph_le_opGraph_of_isClosedExtension
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.clGraph_le_opGraph_of_isClosedExtension {T : D →ₗ[ℂ] F} {A : Dom →ₗ[ℂ] F}
    (h : IsClosedExtension T A) : clGraph T ≤ opGraph A := by sorry
