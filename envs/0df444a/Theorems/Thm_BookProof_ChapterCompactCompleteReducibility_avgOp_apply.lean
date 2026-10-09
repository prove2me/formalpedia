-- Prove2me | Theorems.Thm_BookProof_ChapterCompactCompleteReducibility_avgOp_apply
-- name    : BookProof.ChapterCompactCompleteReducibility.avgOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T22:15:42.733485+00:00
-- url     : https://prove2.me/theorems/c5a4ad82-db1c-4d1b-bd85-ee35f755e664
-- title:
--   `BookProof.ChapterCompactCompleteReducibility.avgOp_apply` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) (v : V) : avgOp μ ρ T v = ∫ g,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterCompactCompleteReducibility`.
--
--   `BookProof.ChapterCompactCompleteReducibility.avgOp_apply` {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V)) (T : V →L[ℂ] V) (v : V) : avgOp μ ρ T v = ∫ g, ρ g (T ((ρ g).symm v)) ∂μ
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterCompactCompleteReducibility.avgOp_apply`.

-- Generated from ChapterCompactCompleteReducibility.lean — theorem BookProof.ChapterCompactCompleteReducibility.avgOp_apply
import Mathlib
import Definitions.Def_ChapterCompactCompleteReducibility
open BookProof.ChapterCompactCompleteReducibility



open MeasureTheory

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsProbabilityMeasure μ]
  [μ.IsMulLeftInvariant]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]


omit [μ.IsMulLeftInvariant] [FiniteDimensional ℂ V] in

theorem BookProof.ChapterCompactCompleteReducibility.avgOp_apply {ρ : G →* (V ≃L[ℂ] V)} (hρ : Continuous fun g => (ρ g : V →L[ℂ] V))
    (T : V →L[ℂ] V) (v : V) :
    avgOp μ ρ T v = ∫ g, ρ g (T ((ρ g).symm v)) ∂μ := by sorry
