-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeCasimirAverage_inner_casimir
-- name    : BookProof.ChapterGaugeCasimirAverage.inner_casimir
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T10:53:37.841982+00:00
-- url     : https://prove2.me/theorems/86b01bf1-8f5f-464c-b1b9-8c8f086fa307
-- title:
--   `BookProof.ChapterGaugeCasimirAverage.inner_casimir` (T : ι → V →ₗ[ℂ] V) (hT : ∀ a, (T a).IsSymmetric) (v : V) : ⟪v, casimir T v⟫_ℂ = ((∑ a, ‖T a v‖ ^ 2 : ℝ) : ℂ)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeCasimirAverage`.
--
--   `BookProof.ChapterGaugeCasimirAverage.inner_casimir` (T : ι → V →ₗ[ℂ] V) (hT : ∀ a, (T a).IsSymmetric) (v : V) : ⟪v, casimir T v⟫_ℂ = ((∑ a, ‖T a v‖ ^ 2 : ℝ) : ℂ)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeCasimirAverage.inner_casimir`.

-- Generated from ChapterGaugeCasimirAverage.lean — theorem BookProof.ChapterGaugeCasimirAverage.inner_casimir
import Definitions.Def_ChapterGaugeIncompleteFixing
import Mathlib
import Definitions.Def_ChapterGaugeCasimirAverage
open BookProof.ChapterGaugeCasimirAverage



open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.ChapterGaugeCasimirAverage.inner_casimir (T : ι → V →ₗ[ℂ] V) (hT : ∀ a, (T a).IsSymmetric) (v : V) :
    ⟪v, casimir T v⟫_ℂ = ((∑ a, ‖T a v‖ ^ 2 : ℝ) : ℂ) := by sorry
