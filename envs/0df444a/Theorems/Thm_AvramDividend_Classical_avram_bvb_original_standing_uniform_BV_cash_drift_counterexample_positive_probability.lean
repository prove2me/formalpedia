-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_standing_uniform_BV_cash_drift_counterexample_positive_probability
-- name    : AvramDividend.Classical.avram_bvb_original_standing_uniform_BV_cash_drift_counterexample_positive_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:26:40.690502+00:00
-- url     : https://prove2.me/theorems/e3079f50-ec57-4aa6-87e6-8fb3c468d5e4
-- title:
--   Standing BV unit-uniform original Lévy source has positive-probability original physical zero-contact cash drift budget failure
-- statement:
--   There exists a genuine original standing BV unit-drift compound-Poisson spectrally negative Lévy process for which the exact original zero-barrier, finite-cap, tenth-horizon physical-grid stopped cash and strict surviving terminal has a positive probability of a nonvanishing excess over the candidate and its true drift-only physical ledger. This directly contradicts any universal a.e drift-only contact-budget claim in the original BV mission.
-- source:
--   Combine Proved original uniform Standing BV positive-probability nojump linear source 2005befa and Proved positive-probability source-physical drift cash failure bridge 5bf44e27, preserving exact original marked source, right dividend, Stieltjes cash, ruin time, and physical-grid L.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_positive_nojump_path_witness
import Theorems.Thm_AvramDividend_Classical_avram_b29_original_positive_probability_drift_source_failure
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_original_standing_uniform_BV_cash_drift_counterexample_positive_probability :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧ X.drift = 1 ∧
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
