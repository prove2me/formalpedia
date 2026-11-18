-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_conditional_mark_exponential_poisson_count_cell_20261117
-- name    : AvramDividend.Classical.avram_a27_original_conditional_mark_exponential_poisson_count_cell_20261117
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T21:31:24.502909+00:00
-- url     : https://prove2.me/theorems/68a1b66d-c7ce-4c74-af96-7fbc4c03313b
-- title:
--   Conditional original negative-mark exponential product on each exact physical Poisson count cell
-- statement:
--   On the unchanged original physical Levy path, conditional on having precisely k strictly negative jumps by t, the integrated exponential of their actual total jump sum is the original Poisson(r) singleton mass times m to the power k; the one-mark Laplace factor m is in [0,1] and matches the exact Levy mark intensity. It is an original-space marked point-process conditional-moment theorem. No auxiliary independent mark stream is assumed.
-- source:
--   Exact original finite negative-jump source count and original finite-activity Poisson point-measure conditional marking; mark-rate normalisation already Proved by 7e30288e. Outstanding source obligation is count-conditioned marked moments, not a Poisson count-law surrogate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_conditional_mark_exponential_poisson_count_cell_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hK : Measurable K) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (hRate : (r : ℝ) =
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) ∧
      ∀ k : ℕ,
        (∫ ω in {ω : Ω | K ω = k},
          Real.exp (θ * J ω) ∂P) =
        (poissonMeasure r).real {k} * m ^ k := by sorry
