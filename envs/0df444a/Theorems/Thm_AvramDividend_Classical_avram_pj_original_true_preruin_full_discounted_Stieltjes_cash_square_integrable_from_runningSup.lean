-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_true_preruin_full_discounted_Stieltjes_cash_square_integrable_from_runningSup
-- name    : AvramDividend.Classical.avram_pj_original_true_preruin_full_discounted_Stieltjes_cash_square_integrable_from_runningSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:04:04.023397+00:00
-- url     : https://prove2.me/theorems/b6e701c7-2794-4baf-a7b2-dde348266853
-- title:
--   Actual strictly pre-ruin full discounted Stieltjes cash has finite second moment from original bounded-horizon Lévy supremum
-- statement:
--   The exact original discounted full right-payment Stieltjes cash at any random physical horizon rho bounded by n that is strictly before actual ruin on every path has a finite squared mean under the original unbounded-variation spectrally negative Levy law. The original cash is nonnegative and bounded by rightLimit D(rho), which is at most x+runningSup X rho by the true pre-ruin reserve; the original runningSup is nondecreasing and the true supremum up to n has finite first and second moments by existing original Levy exponential moment certificates. The original cash square is thus dominated by an integrable quadratic envelope. This supplies a sound L2 source for the positive-clock strictly pre-ruin part of c2a65023 without Gaussian replacement. The theorem explicitly requires strict survival; ruin-contact and zero-clock branches remain separate.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_true_preruin_full_discounted_Stieltjes_cash_square_integrable_from_runningSup
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρle : ∀ ω, ρ ω ≤ n)
    (hρpre : ∀ ω, (ρ ω : ℝ≥0∞) <
      ruinTime X x D ω)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashMeas : Measurable Cash) :
    Integrable (fun ω => (Cash ω)^2) P := by sorry
