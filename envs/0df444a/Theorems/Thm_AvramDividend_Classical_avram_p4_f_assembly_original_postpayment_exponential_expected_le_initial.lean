-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_postpayment_exponential_expected_le_initial
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_postpayment_exponential_expected_le_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:48:57.216871+00:00
-- url     : https://prove2.me/theorems/016f239f-0020-45a3-8959-4f2e8da26c2a
-- title:
--   Original postpayment discounted Lévy exponential expected value is bounded by exponential initial capital
-- statement:
--   For the original Lévy X and actual admissible dividend path D, use the accepted source discounted postpayment exponential supermartingale and nonnegative initial right dividend to show that every deterministic-time discounted exponential has expected value at most exp(θx). The process is genuinely the original source; this is a deterministic-horizon bound, not a random-clock optional stopping theorem and not a substitute for the full w Itô–Meyer signed budget.
-- source:
--   Original postpayment discounted exponential supermartingale fab320c3; source nonnegative cumulative dividends 716ba871 and dividend le rightLimit 953f0e91; pinned Mathlib Supermartingale.setIntegral_le and integral_mono_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_postPayment_discounted_exponential_supermartingale
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_postpayment_exponential_expected_le_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (t : ℝ≥0) :
    (∫ ω, Real.exp
      (θ * (x + X.X t ω - rightLimit D t ω) - (t : ℝ) * q) ∂P) ≤
    Real.exp (θ * x) := by sorry
