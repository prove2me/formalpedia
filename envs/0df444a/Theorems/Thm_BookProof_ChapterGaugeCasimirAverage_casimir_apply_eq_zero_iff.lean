-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeCasimirAverage_casimir_apply_eq_zero_iff
-- name    : BookProof.ChapterGaugeCasimirAverage.casimir_apply_eq_zero_iff
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-08T10:53:33.713094+00:00
-- url     : https://prove2.me/theorems/e4253249-14d0-45dc-aec9-5c3d8b33e1d2
-- title:
--   `BookProof.ChapterGaugeCasimirAverage.casimir_apply_eq_zero_iff` (T : ι → V →ₗ[ℂ] V) (hT : ∀ a, (T a).IsSymmetric) (v : V) : casimir T v = 0 ↔ ∀ a, T a v = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeCasimirAverage`.
--
--   `BookProof.ChapterGaugeCasimirAverage.casimir_apply_eq_zero_iff` (T : ι → V →ₗ[ℂ] V) (hT : ∀ a, (T a).IsSymmetric) (v : V) : casimir T v = 0 ↔ ∀ a, T a v = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeCasimirAverage.casimir_apply_eq_zero_iff`.

-- Generated from ChapterGaugeCasimirAverage.lean — theorem BookProof.ChapterGaugeCasimirAverage.casimir_apply_eq_zero_iff
import Definitions.Def_ChapterGaugeIncompleteFixing
import Mathlib
import Definitions.Def_ChapterGaugeCasimirAverage
open BookProof.ChapterGaugeCasimirAverage



open BookProof.ChapterGaugeIncompleteFixing
open MeasureTheory
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*} [Fintype ι]

theorem BookProof.ChapterGaugeCasimirAverage.casimir_apply_eq_zero_iff (T : ι → V →ₗ[ℂ] V) (hT : ∀ a, (T a).IsSymmetric)
    (v : V) : casimir T v = 0 ↔ ∀ a, T a v = 0 := by sorry
