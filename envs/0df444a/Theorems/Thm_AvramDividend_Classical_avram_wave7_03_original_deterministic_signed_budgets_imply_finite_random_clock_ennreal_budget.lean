-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_ennreal_budget
-- name    : AvramDividend.Classical.avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_ennreal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:47:23.660588+00:00
-- url     : https://prove2.me/theorems/8b08ddbf-d82a-421a-b64a-1eed3987f1b2
-- title:
--   Uniform deterministic signed Stieltjes expected budgets imply full original ENNReal payout budget at finite random clock
-- statement:
--   For the genuine original spectrally negative Lévy process and admissible dividend strategy, suppose a common real B bounds the genuine expected signed discounted Stieltjes payout over the fixed original stopped payment domains paymentTimes(ruinTime)∩Iic(n+1) for every integer n. Then for every measurable pathwise finite NNReal random clock τ, the full actual double ENNReal discounted ruin-stopped dividend cash on paymentTimes(ruinTime)∩Iic(τ ω) is at most ENNReal.ofReal B. The proof uses the separately Proved monotonicity of real expected signed Stieltjes cash under ordered bounded random clocks to bound the cash on each min(τ,n+1) by the deterministic n+1 budget. It then invokes the already Proved original uniform signed random-truncation budget→full ENNReal bridge. This does not require proving a new HJB budget at the random truncations, nor a deterministic bound on τ. It preserves original P, dividendMeasure, rightLimit at zero, continuous mass and endpoint atoms.
-- source:
--   Original bounded random-clock real expected Stieltjes monotonicity; Proved 2bdab35f original uniform random truncation signed budget→ENNReal cash.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_bounded_random_clock_signed_stieltjes_expected_monotone
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_finite_random_clock_direct_uniform_signed_budget_to_ennreal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_deterministic_signed_budgets_imply_finite_random_clock_ennreal_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ)))
    (B : ℝ)
    (hDetBudget : ∀ n : ℕ,
      (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω) ∩
          Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
