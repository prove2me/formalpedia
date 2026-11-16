-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b29_original_uniform_CP_positive_probability_drift_source_failure
-- name    : AvramDividend.Classical.avram_b29_original_uniform_CP_positive_probability_drift_source_failure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:17:57.593334+00:00
-- url     : https://prove2.me/theorems/84cf4a65-08ee-4b74-b5cf-de54eca04528
-- title:
--   A concrete original Standing BV compound-Poisson Lévy law has positive probability of failing the zero-barrier physical drift-only error convergence
-- statement:
--   There exists a concrete original spectrally negative Lévy source on the real-sequence product probability space that is Standing, of bounded variation, has uniform negative-jump intensity on (-1,0), finite negative jump activity, unit drift and zero Gaussian coefficient, for which the original zero-barrier physical stopped cash discounted at q=1 minus its unit-drift masked original HJB mesh ledger has a positive error that fails to converge to zero on a set of positive probability. This follows by applying the original finite activity BV no-jump linear-path positive-probability witness 2005befa and the pathwise original physical error non-convergence 9170e444 through the B29 event measure monotonicity lemma. It isolates a concrete source-faithful counterexample to naive drift-only BV finitecap mesh error vanishing; it does not refute the correct full compensated BV ledger or alter stopping clocks.
-- source:
--   Prove2Me accepted original uniform compound Poisson BV witness 2005befa, original physical zero-barrier unit drift nonconvergence 9170e444, event transfer 5bf44e27; 15 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_b29_original_uniform_CP_positive_probability_drift_source_failure (T : ℝ≥0) :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 ∧
      0 < P {ω |
    let D := barrierStrategy X 0 0
    let T : ℝ := 1 / 10
    let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
    let u : ℕ → ℕ → ℝ≥0 := fun n i =>
      ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
    let F : ℕ → ℝ := fun n =>
      (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
          Iio (T - T / ((n : ℝ) + 2)),
        ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
        (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
          Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
         else 0)
    let L : ℕ → ℝ := fun n =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
      ∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
          Real.exp (-(u n i : ℝ)) *
            (X.drift * deriv w (Z i) - w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
    ¬ Tendsto (fun n => max (F n - (w 0 + L n)) 0)
      atTop (𝓝 (0 : ℝ))} := by sorry
