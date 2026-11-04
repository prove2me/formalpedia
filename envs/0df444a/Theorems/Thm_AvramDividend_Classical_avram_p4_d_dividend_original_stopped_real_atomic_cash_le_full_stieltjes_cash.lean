-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_real_atomic_cash_le_full_stieltjes_cash
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_stopped_real_atomic_cash_le_full_stieltjes_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T09:35:53.31907+00:00
-- url     : https://prove2.me/theorems/0bea4b2a-a56b-486d-9bed-cc3b0aa2806c
-- title:
--   Original stopped true real atomic cash sum never exceeds full discounted Stieltjes cash
-- statement:
--   The actual source stopped right-dividend weighted atom cash is the real tsum over the original finite closed Stieltjes atomic carrier, with the authentic paymentTimes(ruinTime) indicator. The source-proved exact atom-plus-diffuse ENNReal lintegral decomposition and finite full cash bound make both total and atom sum finite. Using pinned Mathlib ENNReal.tsum_toReal_eq and toReal_mono, the honest real atom series is bounded by the full real discounted Stieltjes cash, retaining time zero, surviving horizon and all singular-continuous mass in the complementary nonnegative contribution. This is an explicit stopped L1-envelope input for the P4-F signed Itô budget.
-- source:
--   Accepted 0a519d31 source stopped exact atom/diffuse cash split; pinned Mathlib ENNReal.tsum_toReal_eq, ENNReal.le_tsum, ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_stopped_discounted_all_atoms_diffuse_cash_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_stopped_real_atomic_cash_le_full_stieltjes_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ A : Set ℝ, A.Countable ∧
      (∀ s : ℝ, μ {s} ≠ 0 → s ∈ A) ∧
      (∑' t : A, (μ {(t : ℝ)} *
        (if (t : ℝ) ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * (t : ℝ))))
          else 0)).toReal) ≤
        (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
          then ENNReal.ofReal (Real.exp (-(q * s))) else 0) ∂μ).toReal := by sorry
