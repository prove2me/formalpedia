-- Prove2me | Theorems.Thm_BookProof_ChapterU_differentiable_trajectory_null
-- name    : BookProof.ChapterU.differentiable_trajectory_null
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:28:57.314093+00:00
-- url     : https://prove2.me/theorems/f2e5acc6-1efb-4819-aaf4-4cbe45024635
-- title:
--   `BookProof.ChapterU.differentiable_trajectory_null` {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (path : Ω → ℝ → ℝ) (hext : ∀ᵐ ω ∂P, ∀ t, ¬...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterU`.
--
--   `BookProof.ChapterU.differentiable_trajectory_null` {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (path : Ω → ℝ → ℝ) (hext : ∀ᵐ ω ∂P, ∀ t, ¬ DifferentiableAt ℝ (path ω) t) : P {ω | ∃ t, DifferentiableAt ℝ (path ω) t} = 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterU.differentiable_trajectory_null`.

-- Generated from ChapterU.lean — theorem BookProof.ChapterU.differentiable_trajectory_null
import Mathlib
import Definitions.Def_ChapterU
open BookProof.ChapterU


open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

variable {X : Type*} [MeasurableSpace X]
variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem BookProof.ChapterU.differentiable_trajectory_null {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (path : Ω → ℝ → ℝ)
    (hext : ∀ᵐ ω ∂P, ∀ t, ¬ DifferentiableAt ℝ (path ω) t) :
    P {ω | ∃ t, DifferentiableAt ℝ (path ω) t} = 0 := by sorry
