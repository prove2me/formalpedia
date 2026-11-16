-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:45:33.439259+00:00
-- url     : https://prove2.me/theorems/9170e444-655b-439c-b611-fc36d7237cbc
-- title:
--   Original finite-cap unit-uniform nojump zero-barrier cash positive error fails to converge to zero despite exact physical drift ledger zero
-- statement:
--   For any original unit-drift spectrally negative Lévy process on an exact linear no-jump path to time one, with zero-barrier dividends and cap 1, the exact physical strict-horizon stopped cash plus half-unit surviving terminal exceeds the initial half-unit candidate while the original drift-only masked physical grid L is zero. Therefore the positive part of their excess cannot converge to zero. This is the source-exact failure of the asserted survivor zero-contact BV physical budget.
-- source:
--   Combine the source-exact stopped cash-plus-terminal lower bound with original zero-prepayment masked physical drift-ledger L=0 on the exact unit-linear nojump source and the Proved uniform tenth-horizon nonconvergence lemma. All physical mesh and risk/stopping definitions remain original.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift) :
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
      atTop (𝓝 (0 : ℝ)) := by sorry
