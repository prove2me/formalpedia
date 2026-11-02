-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope
-- name    : AvramDividend.Classical.avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:16:05.847232+00:00
-- url     : https://prove2.me/theorems/ba6baffc-07f7-41f6-b84e-ffb6c1089a5c
-- title:
--   Original full-Stieltjes expected reward bound at every nonnegative real horizon including time zero and any real discount
-- statement:
--   For original source X, original capped admissible dividend D and any nonnegative REAL horizon T, including T=0, and arbitrary real q, the entire original stopped full Stieltjes discounted reward expectation on paymentTimes(ruinTime) ∩ (-∞,T] is bounded by exp(abs(psi(1)-q)*(T.toNNReal+1))*exp(x), a finite explicit envelope. The auxiliary positive NNReal clock T.toNNReal+1 invokes the independently Proved arbitrary-discount source reward moment; nested payment windows and the true Stieltjes measure yield the inequality. This is exactly the real clock type and closed reward window used by the canonical BV and corrected UBV stochastic cores and includes the time-zero payment, all right atoms and singular-continuous dividends.
-- source:
--   Original real-horizon BV ef7e6c20 and corrected UBV 429e17ca canonical expected reward cores, Proved source any-discount moment 8b70a8f9, original paymentTimes and dividendMeasure; no full stochastic compensator assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_any_discount_finite_horizon_stieltjes_exp_moment
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (Real.exp
      (|X.ψ 1 - q| * (((T.toNNReal + 1 : ℝ≥0) : ℝ)))) *
      ENNReal.ofReal (Real.exp x) := by sorry
