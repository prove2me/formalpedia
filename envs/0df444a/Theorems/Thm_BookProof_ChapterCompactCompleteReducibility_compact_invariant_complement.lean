-- Prove2me | Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_compact_invariant_complement
-- name    : BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:16:11.565772+00:00
-- url     : https://prove2.me/theorems/55a24396-1e54-44e9-bd8a-6804b72f9a02
-- title:
--   `BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (μ : Measure G) [IsProbabilityMeasur
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCompactCompleteReducibility`.
--
--   `BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (μ : Measure G) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] (W : Submodule ℂ V) (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) : ∃ W' : Submodule ℂ V, (∀ g : G, ∀ x ∈ W', ρ g x ∈ W') ∧ IsCompl W W'
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement`.

-- Generated from ChapterCompactCompleteReducibility.lean — theorem BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
open BookProof.ChapterCompactCompleteReducibility



open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement {ρ : G →* (V ≃L[ℂ] V)}
    (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] (W : Submodule ℂ V) (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ W' : Submodule ℂ V, (∀ g : G, ∀ x ∈ W', ρ g x ∈ W') ∧ IsCompl W W' := by sorry
