-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_same_source_HJB_and_positive_cash_budget_failure
-- name    : AvramDividend.Classical.avram_bvb_original_uniform_same_source_HJB_and_positive_cash_budget_failure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:07:03.194977+00:00
-- url     : https://prove2.me/theorems/0fb56f67-8141-4a0b-938d-a5d5a1e2695d
-- title:
--   Genuine original Standing BV source jointly meets full HJB verification assumptions and has positive-probability drift-only physical cash failure
-- statement:
--   The same genuine original Standing BV finite-activity spectrally negative Lévy source simultaneously meets the complete finite-cap affine HJB regularity, positivity and right-payment conditions, and carries a positive-probability path where the exact stopped Stieltjes cash surplus over the original drift-only physical ledger does not converge to zero. Hence the zero-contact dividend verification leaf lacks the necessary compensator allowance.
-- source:
--   Combine the Proved original uniform source construction, finite-cap affine HJB bundle, and Proved direct positive-probability original stopped physical-grid cash failure for the same source. No independent existential witnesses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b29_original_positive_probability_drift_source_failure
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_original_uniform_same_source_HJB_and_positive_cash_budget_failure :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 ∧
      0 < P {ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ∧
        (∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) * X.drift)} ∧
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
          atTop (𝓝 (0 : ℝ))} ∧
      (let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
       let D := barrierStrategy X 0 0
       let C : ℝ≥0∞ := 1
       ContinuousOn w (Ici 0) ∧ 0 ≤ w 0 ∧
         (∀ z : ℝ, z < 0 → w z = 0) ∧
         ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
         (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
           X.GeneratorIntegrable w y ∧ X.generator w y - w y ≤ 0) ∧
         (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
         IsAdmissibleLe X 0 C D ∧
         (∀ ω (t : ℝ≥0), 0 < t →
           (t : ℝ≥0∞) < ruinTime X 0 D ω →
           0 ≤ w (riskProcess X 0 D t ω)) ∧
         (∀ ω (t : ℝ≥0),
           (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X 0 D ω) →
           rightLimit D t ω - D t ω ≤
             w (riskProcess X 0 D t ω) -
               w (riskProcess X 0 D t ω -
                 (rightLimit D t ω - D t ω)))) := by sorry
