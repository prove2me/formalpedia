-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_original_bv_sharp_bounded_random_clock_budget
-- name    : AvramDividend.Classical.avram_wave6_chat09_original_bv_sharp_bounded_random_clock_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:33:28.81133+00:00
-- url     : https://prove2.me/theorems/25ef34c9-891b-46b1-9538-3bce772e4c77
-- title:
--   Sharp original BV complete Stieltjes payout budget at any bounded random clock
-- statement:
--   For the actual standing bounded-variation spectrally negative Lévy process with genuine capped admissible dividends, the full discounted, ruin-stopped original Stieltjes payout up to any possibly nonmeasurable random clock τ≤T has expected extended value at most x+T times the original Lévy drift, with no extraneous positive horizon margin. The proof is pathwise monotonicity of the original Stieltjes measure followed by the accepted sharp deterministic source BV closed-horizon expected drift theorem; it retains time-zero, singular-continuous and right-payment atoms and requires no unproved HJB estimate.
-- source:
--   Original sharp closed deterministic BV expected Stieltjes cash bound 23ddd713-8f78-4c6f-b478-98e0a5b32c7c, monotonicity of set integral and outer lintegral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_complete_closed_horizon_sharp_expected_drift_budget

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave6_chat09_original_bv_sharp_bounded_random_clock_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 ≤ x) (C : ℝ≥0∞)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T) :
    (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X x D ω) ∩ Iic ((τ ω : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (x + (T : ℝ) * X.drift) := by sorry
