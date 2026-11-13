-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
-- name    : AvramDividend.Classical.avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T19:10:43.672938+00:00
-- url     : https://prove2.me/theorems/c5eeb765-5190-4597-96a6-1cdd466e7fb5
-- title:
--   Original finite-cap stopped cash plus fixed physical T terminal is almost everywhere increasing in uniform mesh
-- statement:
--   On the original spectrally-negative Lévy process and admissible dividend strategy, the strict stopped discounted Stieltjes cash truncated at the physical uniform inner horizon increases pathwise almost everywhere as the grid refines. The same T-time terminal payoff is added on both sides, so the complete original cash-plus-T-terminal F(n) is nondecreasing. Uses verified full cash finiteness to justify toReal monotonicity; preserves zero right-dividend, singular dividends, ruin jump and T endpoint without additional assumptions on the driving process.
-- source:
--   Proved original full discounted Stieltjes cash ae finite f0d4c94c and Proved bvb45 strict cash toReal monotonicity ab860631.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_strict_discounted_cash_toReal_mono
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb47_original_physical_cash_plus_T_terminal_ae_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q T : ℝ) (hT : 0 < T) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0)
    ∀ᵐ ω ∂P, ∀ n k : ℕ, n ≤ k → F n ω ≤ F k ω := by sorry
