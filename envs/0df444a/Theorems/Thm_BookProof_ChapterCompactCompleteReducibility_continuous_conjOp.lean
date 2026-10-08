-- Prove2me | Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_continuous_conjOp
-- name    : BookProof.ChapterCompactCompleteReducibility.continuous_conjOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:15:25.073208+00:00
-- url     : https://prove2.me/theorems/e0cf069d-8341-49a1-bc97-6a876cb183cf
-- title:
--   `BookProof.ChapterCompactCompleteReducibility.continuous_conjOp` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) : Continuous (conjOp ρ T)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCompactCompleteReducibility`.
--
--   `BookProof.ChapterCompactCompleteReducibility.continuous_conjOp` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) : Continuous (conjOp ρ T)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCompactCompleteReducibility.continuous_conjOp`.

-- Generated from ChapterCompactCompleteReducibility.lean — theorem BookProof.ChapterCompactCompleteReducibility.continuous_conjOp
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
open BookProof.ChapterCompactCompleteReducibility



open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]


omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [FiniteDimensional ℂ V] in

theorem BookProof.ChapterCompactCompleteReducibility.continuous_conjOp {ρ : G →* (V ≃L[ℂ] V)}
    (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) :
    Continuous (conjOp ρ T) := by sorry
