-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_mem_adjGraph_iff
-- name    : BookProof.ClosureUniqueness.mem_adjGraph_iff
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T09:32:14.088983+00:00
-- url     : https://prove2.me/theorems/a59742ee-2612-4788-905b-716703217228
-- title:
--   `BookProof.ClosureUniqueness.mem_adjGraph_iff` {T : D →ₗ[ℂ] F} {p : F × F} : p ∈ adjGraph T ↔ ∀ v : D, (inner ℂ (T v) p.1 : ℂ) = inner ℂ (v : F) p.2
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.mem_adjGraph_iff` {T : D →ₗ[ℂ] F} {p : F × F} : p ∈ adjGraph T ↔ ∀ v : D, (inner ℂ (T v) p.1 : ℂ) = inner ℂ (v : F) p.2
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.mem_adjGraph_iff`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.mem_adjGraph_iff
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.mem_adjGraph_iff {T : D →ₗ[ℂ] F} {p : F × F} :
    p ∈ adjGraph T ↔ ∀ v : D, (inner ℂ (T v) p.1 : ℂ) = inner ℂ (v : F) p.2 := by sorry
