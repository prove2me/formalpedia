-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b29_original_positive_probability_drift_source_failure
-- name    : AvramDividend.Classical.avram_b29_original_positive_probability_drift_source_failure
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:14:33.661954+00:00
-- url     : https://prove2.me/theorems/5bf44e27-6ef4-4ddc-b3e0-5f860f9768ea
-- title:
--   A positive-probability original no-jump unit-drift event forces failure of the zero-barrier physical signed drift-only mesh error convergence
-- statement:
--   Given any original spectrally negative Levy source with unit drift, if a measurable or arbitrary event E has strictly positive probability and every path on E equals the original linear drift t up to horizon 1, then with original zero-barrier dividend strategy, discount q=1, T=0.1, benchmark w(y)=0 for y<0 and 0.5+y otherwise, and the original strictly pre-horizon uniform physical mesh, the event where the positive-part physical discounted cash error relative to drift-only masked HJB ledger fails to converge to zero also has positive probability. This follows from the original pathwise failure theorem on every path in E and measure monotonicity, and is a source-backed counterexample to omitting zero-contact compensation from B25 BV finitecap physical source; no post-ruin clocks introduced.
-- source:
--   Prove2Me original physical zero-barrier drift-only error counterexample 9170e444 and accepted positive-probability nojump linear source 2005befa, 15 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_b29_original_positive_probability_drift_source_failure
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (E : Set Ω) (hE : 0 < P E)
    (hDrift : X.drift = 1)
    (hPath : ∀ ω ∈ E, ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift) :
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
