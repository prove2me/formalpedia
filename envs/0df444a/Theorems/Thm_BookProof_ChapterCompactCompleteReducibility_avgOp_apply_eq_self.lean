-- Prove2me | Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_avgOp_apply_eq_self
-- name    : BookProof.ChapterCompactCompleteReducibility.avgOp_apply_eq_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:16:05.016928+00:00
-- url     : https://prove2.me/theorems/75406080-b331-4064-8e58-857ed14cfa6f
-- title:
--   `BookProof.ChapterCompactCompleteReducibility.avgOp_apply_eq_self` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) {W : Submodule ℂ V} {T : V →L[ℂ] V} (hTid...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCompactCompleteReducibility`.
--
--   `BookProof.ChapterCompactCompleteReducibility.avgOp_apply_eq_self` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) {W : Submodule ℂ V} {T : V →L[ℂ] V} (hTid : ∀ w ∈ W, T w = w) (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) {w : V} (hw : w ∈ W) : avgOp μ ρ T w = w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCompactCompleteReducibility.avgOp_apply_eq_self`.

-- Generated from ChapterCompactCompleteReducibility.lean — theorem BookProof.ChapterCompactCompleteReducibility.avgOp_apply_eq_self
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
open BookProof.ChapterCompactCompleteReducibility



open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem BookProof.ChapterCompactCompleteReducibility.avgOp_apply_eq_self {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V))
    {W : Submodule ℂ V} {T : V →L[ℂ] V} (hTid : ∀ w ∈ W, T w = w)
    (hW : ∀ g : G, ∀ x ∈ W, ρ g x ∈ W) {w : V} (hw : w ∈ W) :
    avgOp μ ρ T w = w := by sorry
