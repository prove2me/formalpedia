-- Prove2me | Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_compact_invariant_complement_haar
-- name    : BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement_haar
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:16:53.524983+00:00
-- url     : https://prove2.me/theorems/ddee28cb-0aa5-4399-987a-f07d62bf6b7d
-- title:
--   `BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement_haar` [T2Space G] {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (W : Submodule ℂ V)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCompactCompleteReducibility`.
--
--   `BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement_haar` [T2Space G] {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (W : Submodule ℂ V) (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) : ∃ W' : Submodule ℂ V, (∀ g : G, ∀ x ∈ W', ρ g x ∈ W') ∧ IsCompl W W'
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement_haar`.

-- Generated from ChapterCompactCompleteReducibility.lean — theorem BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement_haar
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
open BookProof.ChapterCompactCompleteReducibility



open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem BookProof.ChapterCompactCompleteReducibility.compact_invariant_complement_haar [T2Space G] {ρ : G →* (V ≃L[ℂ] V)}
    (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (W : Submodule ℂ V)
    (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) :
    ∃ W' : Submodule ℂ V, (∀ g : G, ∀ x ∈ W', ρ g x ∈ W') ∧ IsCompl W W' := by sorry
