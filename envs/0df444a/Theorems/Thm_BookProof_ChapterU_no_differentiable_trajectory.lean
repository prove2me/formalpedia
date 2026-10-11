-- Prove2me | Theorems.Thm_BookProof_ChapterU_no_differentiable_trajectory
-- name    : BookProof.ChapterU.no_differentiable_trajectory
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T16:28:51.444739+00:00
-- url     : https://prove2.me/theorems/b27fb7d3-c924-4853-b926-073e262c4833
-- title:
--   `BookProof.ChapterU.no_differentiable_trajectory` {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (path : Ω → ℝ → ℝ) (hext : ∀ᵐ ω ∂P, ∀ t, ¬...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterU`.
--
--   `BookProof.ChapterU.no_differentiable_trajectory` {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (path : Ω → ℝ → ℝ) (hext : ∀ᵐ ω ∂P, ∀ t, ¬ DifferentiableAt ℝ (path ω) t) : P {ω | ∃ t, DifferentiableAt ℝ (path ω) t}ᶜ = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterU.no_differentiable_trajectory`.

-- Generated from ChapterU.lean — theorem BookProof.ChapterU.no_differentiable_trajectory
import Mathlib
import Definitions.Def_ChapterU
open BookProof.ChapterU


open MeasureTheory
open scoped ENNReal ProbabilityTheory TensorProduct

variable {X : Type*} [MeasurableSpace X]
variable (R M N : Type*) [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem BookProof.ChapterU.no_differentiable_trajectory {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (path : Ω → ℝ → ℝ)
    (hext : ∀ᵐ ω ∂P, ∀ t, ¬ DifferentiableAt ℝ (path ω) t) :
    P {ω | ∃ t, DifferentiableAt ℝ (path ω) t}ᶜ = 1 := by sorry
