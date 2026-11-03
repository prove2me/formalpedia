-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_outer_cash_eq_iSup_bounded_cash
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_outer_cash_eq_iSup_bounded_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:53:26.854637+00:00
-- url     : https://prove2.me/theorems/8d65770f-5db5-4a71-9583-9fc782d92ab4
-- title:
--   Original finite random-clock outer Stieltjes ENNReal cash is supremum of bounded-clock cash
-- statement:
--   For the exact original Lévy process, any genuine dividend strategy and any measurable finite NNReal random clock τ, the double ENNReal Stieltjes payout over the original stopped payment set equals the supremum of the same double ENNReal payouts at bounded clocks min τ (n+1). Measurability follows from the original full Stieltjes random upper-clock theorem; monotone convergence uses the canonical P and dividendMeasure. Since truncations eventually equal τ on each path, all time-zero, continuous and endpoint masses survive.
-- source:
--   Proved original source random-clock cash measurability and Proved 09b8cab7 atom-preserving pathwise finite-clock truncation, Mathlib lintegral_iSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_outer_cash_eq_iSup_bounded_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ⨆ n : ℕ, (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by sorry
