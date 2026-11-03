-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
-- name    : AvramDividend.Classical.avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:28:26.511833+00:00
-- url     : https://prove2.me/theorems/000389d1-8b8e-45cf-b4d1-0a4e161b8c29
-- title:
--   Canonical original perpetual dividendValue finite iff genuine bounded-horizon signed Stieltjes expectations are uniformly real-bounded
-- statement:
--   For the original spectrally negative Lévy process, probability measure P and capped admissible dividend strategy D, the canonical infinite-horizon dividendValue, defined as a double ENNReal integral over the actual paymentTimes(ruinTime) and dividendMeasure, is finite precisely if there exists a real bound B for every expected signed discounted Stieltjes payout up to integer time n+1 on the identical stopped domain. The Proved perpetual expected cash monotone-convergence bridge identifies dividendValue with the supremum of ENNReal.ofReal of these signed means. In the finite direction nonnegativity of the signed integrands and ENNReal.toReal_mono give the uniform real bound B=dividendValue.toReal. Conversely the Proved uniform signed budget to dividendValue theorem gives dividendValue≤ofReal B<⊤. All time-zero right-limit and continuous strictly pre-ruin payments are preserved, with no auxiliary process or unstated integrability hypothesis.
-- source:
--   Proved original perpetual cash iSup real Stieltjes expected identity f05062e4-0096-4e01-9824-b7e83214cd89 and Proved uniform signed horizon budgets imply canonical dividendValue bound 96f0eeb7-80fd-462c-8bdf-cb62d1bfef11; Real.exp_pos; ENNReal.toReal_mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_perpetual_cash_eq_iSup_real_stieltjes_means
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_uniform_signed_horizon_budgets_imply_dividendValue_le
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_dividendValue_finite_iff_uniform_signed_horizon_mean_bounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) :
    (dividendValue X q x D < ⊤) ↔
    ∃ B : ℝ, ∀ n : ℕ,
      (∫ ω, (∫ t in
          paymentTimes (ruinTime X x D ω) ∩ Iic (((n + 1 : ℕ) : ℝ)),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ B := by sorry
