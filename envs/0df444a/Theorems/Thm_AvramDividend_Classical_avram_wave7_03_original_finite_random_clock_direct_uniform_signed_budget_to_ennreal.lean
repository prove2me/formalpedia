-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
-- name    : AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:06:14.244604+00:00
-- url     : https://prove2.me/theorems/2bdab35f-a0df-4b24-a3c1-64fcc5c0299c
-- title:
--   Original finite random-clock uniform signed bounded Stieltjes budget implies full ENNReal cash budget
-- statement:
--   Suppose the expected original signed discounted Stieltjes cash over each truly bounded random stopped domain paymentTimes(ruinTime)∩Iic(min τ (n+1)) is at most a common B, with τ arbitrary measurable and pointwise finite but not uniformly bounded. Then the full original double ENNReal cash over paymentTimes(ruinTime)∩Iic τ is ≤ ENNReal.ofReal B. The proof directly combines the Proved exact original outer ENNReal monotone convergence bridge 8d65770f and the independently Proved original bounded clock signed/ENNReal mean equivalence fc7c1b8a term by term; no import of an Open unbounded signed bridge.
-- source:
--   Proved original finite-clock outer monotone cash 8d65770f; Proved original bounded random-clock signed-ENNReal expectation fc7c1b8a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_outer_cash_eq_iSup_bounded_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hBound : ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩
          Iic ((min (τ ω) (((n + 1 : ℕ) : ℝ≥0)) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
