-- Prove2me | Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_avgOp_comm
-- name    : BookProof.ChapterCompactCompleteReducibility.avgOp_comm
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:16:15.52599+00:00
-- url     : https://prove2.me/theorems/5a8a3dc5-9ecc-4e8d-b7f5-04da059d9d96
-- title:
--   `BookProof.ChapterCompactCompleteReducibility.avgOp_comm` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) (h : G) (v : V) : avgOp μ ρ T (ρ h v)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCompactCompleteReducibility`.
--
--   `BookProof.ChapterCompactCompleteReducibility.avgOp_comm` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) (h : G) (v : V) : avgOp μ ρ T (ρ h v) = ρ h (avgOp μ ρ T v)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCompactCompleteReducibility.avgOp_comm`.

-- Generated from ChapterCompactCompleteReducibility.lean — theorem BookProof.ChapterCompactCompleteReducibility.avgOp_comm
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
open BookProof.ChapterCompactCompleteReducibility



open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem BookProof.ChapterCompactCompleteReducibility.avgOp_comm {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V))
    (T : V →L[ℂ] V) (h : G) (v : V) :
    avgOp μ ρ T (ρ h v) = ρ h (avgOp μ ρ T v) := by sorry
