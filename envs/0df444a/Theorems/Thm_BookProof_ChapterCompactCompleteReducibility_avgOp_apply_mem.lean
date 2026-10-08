-- Prove2me | Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_avgOp_apply_mem
-- name    : BookProof.ChapterCompactCompleteReducibility.avgOp_apply_mem
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:16:10.264425+00:00
-- url     : https://prove2.me/theorems/c6ab92af-ebbd-47a4-8e95-cae5c98662aa
-- title:
--   `BookProof.ChapterCompactCompleteReducibility.avgOp_apply_mem` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) {W : Submodule ℂ V} {T : V →L[ℂ] V} (hT : ∀ v, T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCompactCompleteReducibility`.
--
--   `BookProof.ChapterCompactCompleteReducibility.avgOp_apply_mem` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) {W : Submodule ℂ V} {T : V →L[ℂ] V} (hT : ∀ v, T v ∈ W) (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) (v : V) : avgOp μ ρ T v ∈ W
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCompactCompleteReducibility.avgOp_apply_mem`.

-- Generated from ChapterCompactCompleteReducibility.lean — theorem BookProof.ChapterCompactCompleteReducibility.avgOp_apply_mem
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
open BookProof.ChapterCompactCompleteReducibility



open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem BookProof.ChapterCompactCompleteReducibility.avgOp_apply_mem {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V))
    {W : Submodule ℂ V} {T : V →L[ℂ] V} (hT : ∀ v, T v ∈ W)
    (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) (v : V) :
    avgOp μ ρ T v ∈ W := by sorry
