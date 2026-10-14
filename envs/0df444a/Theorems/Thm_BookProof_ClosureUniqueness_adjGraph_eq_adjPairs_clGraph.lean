-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_adjGraph_eq_adjPairs_clGraph
-- name    : BookProof.ClosureUniqueness.adjGraph_eq_adjPairs_clGraph
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:44:49.364329+00:00
-- url     : https://prove2.me/theorems/b5a9ef8d-d2aa-4038-91c6-e447842813fb
-- title:
--   `BookProof.ClosureUniqueness.adjGraph_eq_adjPairs_clGraph` (T : D →ₗ[ℂ] F) : adjGraph T = adjPairs (clGraph T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.adjGraph_eq_adjPairs_clGraph` (T : D →ₗ[ℂ] F) : adjGraph T = adjPairs (clGraph T)
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.adjGraph_eq_adjPairs_clGraph`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.adjGraph_eq_adjPairs_clGraph
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.adjGraph_eq_adjPairs_clGraph (T : D →ₗ[ℂ] F) : adjGraph T = adjPairs (clGraph T) := by sorry
