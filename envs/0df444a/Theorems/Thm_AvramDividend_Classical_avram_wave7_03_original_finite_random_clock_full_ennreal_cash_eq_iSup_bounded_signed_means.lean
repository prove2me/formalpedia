-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_full_ennreal_cash_eq_iSup_bounded_signed_means
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_full_ennreal_cash_eq_iSup_bounded_signed_means
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:47:37.005603+00:00
-- url     : https://prove2.me/theorems/7073f4ce-7dc6-4cfd-9aa2-487352155f33
-- title:
--   Full original ENNReal finite random-clock payout is supremum of exactly bounded signed Stieltjes means
-- statement:
--   For every measurable pathwise finite NNReal random stopping clock at the exact original Levy process and admissible original dividend strategy, the original expected double ENNReal ruin-stopped dividend cash equals the supremum over n of ENNReal.ofReal of the original expected signed Stieltjes payout stopped at the bounded random clock min τ (n+1). This keeps every time-zero, continuous and endpoint atom, because min τ (n+1) eventually equals τ along each path. No global deterministic bound on τ, no proxy probability space, and no signed integral treated as ENNReal without exact full-clock conversion.
-- source:
--   Proved 09b8cab7 pathwise eventually exact finite random-clock truncation; Proved original random-upper-clock measurable cash; Proved fc7c1b8a bounded random-clock original signed-ENNReal mean bridge; Mathlib lintegral_iSup.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_cash_eq_iSup_min_integer_clocks
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_full_ennreal_cash_eq_iSup_bounded_signed_means
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    ⨆ n : ℕ, ENNReal.ofReal
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) := by sorry
