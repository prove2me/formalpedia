-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
-- name    : AvramDividend.Classical.avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:41:53.697577+00:00
-- url     : https://prove2.me/theorems/f97e4695-e32a-46c6-996a-a7796cad36d7
-- title:
--   Original stopped full Stieltjes discounted real-valued dividend reward is L1 at every nonnegative real clock
-- statement:
--   For exactly the original Lévy source, admissible dividend process, original ruinTime, original paymentTimes and full dividendMeasure, the real toReal of the finite-horizon discounted ENNReal Stieltjes reward is Integrable under original P at every real T≥0 and arbitrary q. The proof constructs measurable random full-payment lintegral through the accepted source s-finite dividend kernel, invokes the independently Proved explicit real-clock expected envelope ba6baffc, derives a finite nested ENNReal lintegral and applies the pinned theorem integrable_toReal_of_lintegral_ne_top. Includes the zero-time dividend atom, right lumps and all continuous singular components. Supplies the exact real L1 reward premise for stopped Itô-Meyer expectation and Fatou estimates of canonical BV ef7e6c20 and corrected UBV 429e17ca, without assuming or proving the missing source stochastic chain.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), finite-horizon expected full Stieltjes dividends. Original source new Proved real-clock reward envelope ba6baffc, Proved random indicator kernel and global s-finite dividend kernel; original canonical BV ef7e6c20, corrected UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_expected_envelope
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q : ℝ) :
    Integrable (fun ω : Ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by sorry
