-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
-- name    : AvramDividend.Classical.avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T13:06:24.912203+00:00
-- url     : https://prove2.me/theorems/f05062e4-0096-4e01-9824-b7e83214cd89
-- title:
--   Perpetual original dividend ENNReal cash is supremum of exact finite-horizon real Stieltjes means
-- statement:
--   The original perpetual expected dividend cash (double ENNReal lintegral over exact paymentTimes of ruinTime) equals the supremum over integer horizons n+1 of the ENNReal embeddings of the actual real Stieltjes expected discounted payout on paymentTimes(ruinTime) cap Iic(n+1). Original spectrally negative Levy, original capped admissible dividends, q>=0, no BV/UBV or extra L1/supremum finiteness assumption. The time-zero right-limit atom, continuous and jump dividends and strict positive pre-ruin times are preserved. The identity is valid even with infinite perpetual cash.
-- source:
--   Accepted original pathwise perpetual cash iSup 21a1dc8d; accepted original finite-horizon cash measurability 2d478c7d; W7-03 proved deterministic real/ENNReal expectation 633be7dd; pinned Mathlib lintegral_iSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_perpetual_cash_eq_iSup_integer_truncations
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_deterministic_horizon_mean_consumption

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ⨆ n : ℕ, ENNReal.ofReal
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
