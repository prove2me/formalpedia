-- Prove2me | Theorems.Thm_BookProof_ChapterMAPNull_ae_not_mem_countable_map_set
-- name    : BookProof.ChapterMAPNull.ae_not_mem_countable_map_set
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:49:10.810626+00:00
-- url     : https://prove2.me/theorems/d157a701-801c-4019-b43c-ffdd74d0b641
-- title:
--   `BookProof.ChapterMAPNull.ae_not_mem_countable_map_set` (μ : Measure α) [NullSingletonClass μ] (maximizers : Set α) (hcountable : maximizers.Countable) : ∀ᵐ x ∂μ, x ∉ maximizers
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMAPNull`.
--
--   `BookProof.ChapterMAPNull.ae_not_mem_countable_map_set` (μ : Measure α) [NullSingletonClass μ] (maximizers : Set α) (hcountable : maximizers.Countable) : ∀ᵐ x ∂μ, x ∉ maximizers
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMAPNull.ae_not_mem_countable_map_set`.

-- Generated from ChapterMAPNull.lean — theorem BookProof.ChapterMAPNull.ae_not_mem_countable_map_set
import Mathlib
import Definitions.Def_ChapterMAPNull
open BookProof.ChapterMAPNull


open MeasureTheory


variable {α : Type*} [MeasurableSpace α]

theorem BookProof.ChapterMAPNull.ae_not_mem_countable_map_set (μ : Measure α) [NullSingletonClass μ]
    (maximizers : Set α) (hcountable : maximizers.Countable) :
    ∀ᵐ x ∂μ, x ∉ maximizers := by sorry
