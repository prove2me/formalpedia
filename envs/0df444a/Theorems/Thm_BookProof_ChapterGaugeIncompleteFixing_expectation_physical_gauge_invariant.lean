-- Prove2me | Theorems.Thm_BookProof_ChapterGaugeIncompleteFixing_expectation_physical_gauge_invariant
-- name    : BookProof.ChapterGaugeIncompleteFixing.expectation_physical_gauge_invariant
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-08T11:12:56.094983+00:00
-- url     : https://prove2.me/theorems/db189fe6-c888-49bf-ba49-51b7d43fdc48
-- title:
--   `BookProof.ChapterGaugeIncompleteFixing.expectation_physical_gauge_invariant` {U : G → (H →L[ℂ] H)} (hU : IsGaugeUnitaryFamily U) {A : H →L[ℂ] H} (hA : IsPhysicalOperator U A) (g :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterGaugeIncompleteFixing`.
--
--   `BookProof.ChapterGaugeIncompleteFixing.expectation_physical_gauge_invariant` {U : G → (H →L[ℂ] H)} (hU : IsGaugeUnitaryFamily U) {A : H →L[ℂ] H} (hA : IsPhysicalOperator U A) (g : G) (Ψ : H) : ⟪U g Ψ, A (U g Ψ)⟫_ℂ = ⟪Ψ, A Ψ⟫_ℂ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterGaugeIncompleteFixing.expectation_physical_gauge_invariant`.

-- Generated from ChapterGaugeIncompleteFixing.lean — theorem BookProof.ChapterGaugeIncompleteFixing.expectation_physical_gauge_invariant
import Mathlib
import Definitions.Def_ChapterGaugeIncompleteFixing
open BookProof.ChapterGaugeIncompleteFixing


open scoped InnerProductSpace

variable {X : Type*}
variable (G : Type*) [Group G] [MulAction G X]
variable {G : Type*} [Group G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.ChapterGaugeIncompleteFixing.expectation_physical_gauge_invariant {U : G → (H →L[ℂ] H)}
    (hU : IsGaugeUnitaryFamily U) {A : H →L[ℂ] H} (hA : IsPhysicalOperator U A)
    (g : G) (Ψ : H) :
    ⟪U g Ψ, A (U g Ψ)⟫_ℂ = ⟪Ψ, A Ψ⟫_ℂ := by sorry
