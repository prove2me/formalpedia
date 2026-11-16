-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b29_original_uniform_drift_only_positive_gap_source_certificate
-- name    : AvramDividend.Classical.avram_b29_original_uniform_drift_only_positive_gap_source_certificate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T14:59:32.291542+00:00
-- url     : https://prove2.me/theorems/30cbfb38-8218-481f-bdc0-d3ae91ff22c4
-- title:
--   Original zero-barrier unit-drift no-jump path: strict physical cash plus surviving terminal has a positive lower gap while the masked drift-only source vanishes
-- statement:
--   Under the exact original unit-linear no-jump Lévy source to time 1, with drift 1, barrier zero, constant-plus-linear candidate w and literal ruin-clipped physical mesh up to 0.1, the strict cash plus terminal reward F_n exceeds (0.08+0.5)e^-0.1 for all n≥4; meanwhile the drift-only interior-generator mesh L_n vanishes for every n because the genuine original prepayment reserve is zero. These are the two concrete source calculations necessary to establish nonconvergence of the positive cash excess and diagnose omission of zero-contact boundary terms.
-- source:
--   Prove2Me original zero-barrier no-jump counterexample 9170e444, proved eight-hundredths strict window lemma 191e74ab, zero-reserve lemma 9658aeb1, and strict positive-gap nonconvergence lemma 034f8177 (15 November 2026)

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_b29_original_uniform_drift_only_positive_gap_source_certificate
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
    (∀ n : ℕ, 4 ≤ n →
      (2 / 25 + 1 / 2 : ℝ) * Real.exp (-(1 / 10 : ℝ)) ≤ F n) ∧
    (∀ n : ℕ, L n = 0) := by sorry
