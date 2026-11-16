-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_BV_full_HJB_and_strict_cash_failure_same_source
-- name    : AvramDividend.Classical.avram_bvb_original_uniform_BV_full_HJB_and_strict_cash_failure_same_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T11:05:48.349204+00:00
-- url     : https://prove2.me/theorems/968ed9ce-2464-4164-aa37-637d6c70298a
-- title:
--   One genuine original Standing BV uniform source satisfies HJB and admissibility while positive-probability original stopped cash exceeds drift-only physical ledger
-- statement:
--   Construct the same genuine original Standing BV negative-uniform Lévy source satisfying full finite-cap HJB and admissible zero-barrier dividends while its original clipped discounted Stieltjes cash and survivor terminal strictly exceed the initial candidate plus drift-only physical ledger with positive probability. This proves the two properties coexist on exactly one process, the critical obstruction to omitting jump compensation in the BV survivor contact statement.
-- source:
--   Re-use the entire original Standing BV uniform HJB witness and instantiate the separately Proved positive-probability linear-source stopped cash failure on its own certified nojump event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_source_full_positivecap_HJB_witness
import Theorems.Thm_AvramDividend_Classical_avram_b29_original_positive_probability_drift_source_failure
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_original_uniform_BV_full_HJB_and_strict_cash_failure_same_source :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧ X.drift = 1 ∧
      (let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
       let D := barrierStrategy X 0 0
       (∀ y : ℝ, 0 < y → ENNReal.ofReal y < (1 : ℝ≥0∞) →
          X.GeneratorIntegrable w y ∧ X.generator w y - w y ≤ 0) ∧
       IsAdmissibleLe X 0 (1 : ℝ≥0∞) D) ∧
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
