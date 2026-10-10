-- Prove2me | Theorems.Thm_BookProof_ClosureUniqueness_clGraph_inner_deficiency
-- name    : BookProof.ClosureUniqueness.clGraph_inner_deficiency
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T11:42:13.474341+00:00
-- url     : https://prove2.me/theorems/5c4811a5-6db2-4608-9540-cf9e02c0cbdb
-- title:
--   `BookProof.ClosureUniqueness.clGraph_inner_deficiency` {T : D →ₗ[ℂ] F} {w : F} (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = Complex.I * inner ℂ (v : F) w) {p : F × F} (hp : p ∈ clGraph T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterClosureUniqueness`.
--
--   `BookProof.ClosureUniqueness.clGraph_inner_deficiency` {T : D →ₗ[ℂ] F} {w : F} (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = Complex.I * inner ℂ (v : F) w) {p : F × F} (hp : p ∈ clGraph T) : (inner ℂ p.2 w : ℂ) = Complex.I * inner ℂ p.1 w
--
--   Formalization note: Lean 4 identifier `BookProof.ClosureUniqueness.clGraph_inner_deficiency`.

-- Generated from ChapterClosureUniqueness.lean — theorem BookProof.ClosureUniqueness.clGraph_inner_deficiency
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterClosureUniqueness
import Definitions.Def_ChapterEsaClosureCore
open BookProof.EsaClosure
open BookProof.ClosureUniqueness



open BookProof.FarisLavine BookProof.EsaClosure

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D D₁ D₂ Dom Dom₁ Dom₂ : Submodule ℂ F}

theorem BookProof.ClosureUniqueness.clGraph_inner_deficiency {T : D →ₗ[ℂ] F} {w : F}
    (hw : ∀ v : D, (inner ℂ (T v) w : ℂ) = Complex.I * inner ℂ (v : F) w) {p : F × F}
    (hp : p ∈ clGraph T) : (inner ℂ p.2 w : ℂ) = Complex.I * inner ℂ p.1 w := by sorry
