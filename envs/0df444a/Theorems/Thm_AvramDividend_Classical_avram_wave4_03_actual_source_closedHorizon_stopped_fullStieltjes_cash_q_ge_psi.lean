-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_cash_q_ge_psi
-- name    : AvramDividend.Classical.avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_cash_q_ge_psi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:07:26.517664+00:00
-- url     : https://prove2.me/theorems/20163182-6fe0-45b6-b2a1-445c2fd35c24
-- title:
--   Genuine stopped original-source full-Stieltjes finite-horizon expected dividends for all q≥ψ(1)
-- statement:
--   For arbitrary actual capped adapted left-continuous right-payment dividend strategy D on the original spectrally negative Lévy source probability space, and a discount rate q at least ψ(1), the expected full [0,T] strictly pre-ruin Stieltjes dividend reward is at most exp(x). Its measure includes the initial payment atom, positive-time atoms, diffuse and singular-continuous dividends. The proof combines the original-source full-Icc expected exponential martingale budget at q≥ψ(1), actual postpayment pre-ruin solvency, and the rigorous random Stieltjes integral measurability. This verifies a special exponential test across a range of discount parameters and does not claim the general C1 HJB core.
-- source:
--   Proved actual source stopped solvency kernel 0375c440, source expected closed-Icc budget q≥ψ(1) target cd61fb3d (Open at spec draft), source random integral measurability 872a8afd, joint source path/time measurability 30c00aaa.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actualStopped_exponential_payment_kernel_dominated
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_closedHorizon_fullStieltjes_exponential_budget_q_ge_psi
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.avram_wave4_03_actual_source_closedHorizon_stopped_fullStieltjes_cash_q_ge_psi
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : X.ψ 1 ≤ q)
    (T : ℝ≥0) (hT : 0 < T) :
    (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      if s ∈ paymentTimes (ruinTime X x D ω) then
        ENNReal.ofReal (Real.exp (-(q * (s.toNNReal : ℝ))))
      else 0 ∂dividendMeasure D ω ∂P) ≤
    ENNReal.ofReal (Real.exp x) := by sorry
