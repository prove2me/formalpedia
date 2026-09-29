-- Prove2me | Theorems.Thm_EthierKurtz_levy_type_martingale_well_posed
-- name    : EthierKurtz.levy_type_martingale_well_posed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T06:29:43.776734+00:00
-- url     : https://prove2.me/theorems/77b1b262-3c55-499f-ac89-7c581f1ae890
-- title:
--   Theorem 3.3 — nonautonomous Lévy-type martingale-problem well-posedness
-- statement:
--   For bounded continuous strictly positive-definite covariance, bounded measurable drift, and a weighted jump kernel with the stated integrability and setwise bounded-continuity conditions, every initial probability law admits a measurable-process solution and all such solutions have identical finite-dimensional distributions.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 3, Theorem 3.3 and equation (3.21), printed pp. 379–380 (PDF pp. 388–389).

import Definitions.Def_EthierKurtz_levyTypeOperator
import Definitions.Def_EthierKurtz_SolvesLevyTypeMartingaleProblem

open MeasureTheory Filter
open scoped NNReal Topology ContDiff

namespace EthierKurtz

/-- Full well-posedness, including arbitrary initial probability laws and
uniqueness across arbitrary probability spaces. Setwise continuity of the
weighted measures is retained, not replaced by weak continuity. -/
theorem levy_type_martingale_well_posed (d : ℕ) [NeZero d]
    (a : ℝ≥0 × EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d))
    (b : ℝ≥0 × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ν : ℝ≥0 × EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)))
    (ha : Continuous a) (hb : Measurable b)
    (hbounded : ∃ M : ℝ, ∀ z, ‖a z‖ ≤ M ∧ ‖b z‖ ≤ M)
    (hsym : ∀ z u v, inner ℝ (a z u) v = inner ℝ u (a z v))
    (hpos : ∀ z u, u ≠ 0 → 0 < inner ℝ u (a z u))
    (hfinite : ∀ z, Integrable (fun y : EuclideanSpace ℝ (Fin d) =>
      ‖y‖ ^ 2 / (1 + ‖y‖ ^ 2)) (ν z))
    (hsetwise : ∀ Γ : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet Γ →
      Continuous (fun z => ∫ y in Γ, ‖y‖ ^ 2 / (1 + ‖y‖ ^ 2) ∂(ν z)) ∧
      ∃ M : ℝ, ∀ z, |∫ y in Γ, ‖y‖ ^ 2 / (1 + ‖y‖ ^ 2) ∂(ν z)| ≤ M)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] :
    ∃ (Ω : Type) (m : MeasurableSpace Ω),
      letI : MeasurableSpace Ω := m
      ∃ P : Measure Ω, IsProbabilityMeasure P ∧
        ∃ X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
          SolvesLevyTypeMartingaleProblem a b ν μ P X ∧
          ∀ (Ω' : Type) (m' : MeasurableSpace Ω'),
            letI : MeasurableSpace Ω' := m'
            ∀ Q : Measure Ω', IsProbabilityMeasure Q →
              ∀ Y : ℝ≥0 → Ω' → EuclideanSpace ℝ (Fin d),
                SolvesLevyTypeMartingaleProblem a b ν μ Q Y →
                ∀ (n : ℕ) (t : Fin n → ℝ≥0),
                  Measure.map (fun w i => X (t i) w) P =
                    Measure.map (fun w i => Y (t i) w) Q := by sorry
