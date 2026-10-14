-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_factorGraph_quadForm_nonneg
-- name    : BookProof.ClosureUniqueness.factorGraph_quadForm_nonneg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-11T16:46:14.325396+00:00
-- url     : https://prove2.me/theorems/8702e87a-6803-4644-9427-17b653e0879c
-- title:
--   `BookProof.ClosureUniqueness.factorGraph_quadForm_nonneg` {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorGraph A) : 0 ≤ (inner ℂ p.1 p.2 : ℂ).re ∧ (inner ℂ p.1 p.2 : ℂ).im = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.factorGraph_quadForm_nonneg` {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorGraph A) : 0 ≤ (inner ℂ p.1 p.2 : ℂ).re ∧ (inner ℂ p.1 p.2 : ℂ).im = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.factorGraph_quadForm_nonneg`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.factorGraph_quadForm_nonneg
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.factorGraph_quadForm_nonneg {A : D →ₗ[ℂ] F} {p : F × F} (hp : p ∈ factorGraph A) :
    0 ≤ (inner ℂ p.1 p.2 : ℂ).re ∧ (inner ℂ p.1 p.2 : ℂ).im = 0 := by sorry
