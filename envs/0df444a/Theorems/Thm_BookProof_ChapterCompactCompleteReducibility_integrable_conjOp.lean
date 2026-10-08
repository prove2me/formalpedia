-- Prove2me | Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_integrable_conjOp
-- name    : BookProof.ChapterCompactCompleteReducibility.integrable_conjOp
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T22:15:24.392237+00:00
-- url     : https://prove2.me/theorems/93441356-8617-46f2-bc45-c672582793f0
-- title:
--   `BookProof.ChapterCompactCompleteReducibility.integrable_conjOp` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) : Integrable (conjOp ρ T) μ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCompactCompleteReducibility`.
--
--   `BookProof.ChapterCompactCompleteReducibility.integrable_conjOp` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) : Integrable (conjOp ρ T) μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCompactCompleteReducibility.integrable_conjOp`.

-- Generated from ChapterCompactCompleteReducibility.lean — theorem BookProof.ChapterCompactCompleteReducibility.integrable_conjOp
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
open BookProof.ChapterCompactCompleteReducibility



open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]


omit [μ.IsMulLeftInvariant] [FiniteDimensional ℂ V] in

theorem BookProof.ChapterCompactCompleteReducibility.integrable_conjOp {ρ : G →* (V ≃L[ℂ] V)}
    (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) :
    Integrable (conjOp ρ T) μ := by sorry
