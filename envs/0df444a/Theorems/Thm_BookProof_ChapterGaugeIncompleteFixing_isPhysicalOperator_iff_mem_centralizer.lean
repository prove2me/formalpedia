-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeIncompleteFixing_isPhysicalOperator_iff_mem_centralizer
-- name    : BookProof.ChapterGaugeIncompleteFixing.isPhysicalOperator_iff_mem_centralizer
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T11:12:55.635663+00:00
-- url     : https://prove2.me/theorems/6d51ee20-b066-4ef5-a7bb-978530cca5c8
-- title:
--   `BookProof.ChapterGaugeIncompleteFixing.isPhysicalOperator_iff_mem_centralizer` (U : G → (H →L[ℂ] H)) (A : H →L[ℂ] H) : IsPhysicalOperator U A ↔ A ∈ Subalgebra.centralizer ℂ (Set.r
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeIncompleteFixing`.
--
--   `BookProof.ChapterGaugeIncompleteFixing.isPhysicalOperator_iff_mem_centralizer` (U : G → (H →L[ℂ] H)) (A : H →L[ℂ] H) : IsPhysicalOperator U A ↔ A ∈ Subalgebra.centralizer ℂ (Set.range U)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeIncompleteFixing.isPhysicalOperator_iff_mem_centralizer`.

-- Generated from ChapterGaugeIncompleteFixing.lean — theorem BookProof.ChapterGaugeIncompleteFixing.isPhysicalOperator_iff_mem_centralizer
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing


open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]
variable {G : Type*} [Group G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterGaugeIncompleteFixing.isPhysicalOperator_iff_mem_centralizer (U : G → (H →L[ℂ] H))
    (A : H →L[ℂ] H) :
    IsPhysicalOperator U A ↔ A ∈ Subalgebra.centralizer ℂ (Set.range U) := by sorry
