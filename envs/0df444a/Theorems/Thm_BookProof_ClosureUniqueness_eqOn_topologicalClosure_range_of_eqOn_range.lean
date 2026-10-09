-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_eqOn_topologicalClosure_range_of_eqOn_range
-- name    : BookProof.ClosureUniqueness.eqOn_topologicalClosure_range_of_eqOn_range
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T11:43:34.855056+00:00
-- url     : https://prove2.me/theorems/9758ad1c-0316-4256-823f-08d0e74821b5
-- title:
--   `BookProof.ClosureUniqueness.eqOn_topologicalClosure_range_of_eqOn_range` (B : D →ₗ[ℂ] F) (U V : F →L[ℂ] F) (h : ∀ x : D, U (B x) = V (B x)) : ∀ z ∈ (LinearMap.range B).topological
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.eqOn_topologicalClosure_range_of_eqOn_range` (B : D →ₗ[ℂ] F) (U V : F →L[ℂ] F) (h : ∀ x : D, U (B x) = V (B x)) : ∀ z ∈ (LinearMap.range B).topologicalClosure, U z = V z
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.eqOn_topologicalClosure_range_of_eqOn_range`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.eqOn_topologicalClosure_range_of_eqOn_range
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.eqOn_topologicalClosure_range_of_eqOn_range (B : D →ₗ[ℂ] F) (U V : F →L[ℂ] F)
    (h : ∀ x : D, U (B x) = V (B x)) :
    ∀ z ∈ (LinearMap.range B).topologicalClosure, U z = V z := by sorry
