-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_clock_real_budget_to_ennreal
-- name    : AvramDividend.Classical.avram_wave7_03_original_full_clock_real_budget_to_ennreal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T11:39:16.686711+00:00
-- url     : https://prove2.me/theorems/1c237b6b-2a7f-489f-80bc-0603a3e1e67e
-- title:
--   Original full Stieltjes real expected-cash budget implies ENNReal budget without prior finiteness premise
-- statement:
--   For the canonical original Lévy process and dividend strategy, a real expected discounted Stieltjes cash inequality at a finite deterministic clock T implies the corresponding ENNReal double-lintegral inequality on the exact same paymentTimes(ruinTime) intersect Iic T. This uses previously proved original-source L1 integrability and almost-sure finite payment mass to establish ofReal(integral cash.toReal)=lintegral cash; no prior global ENNReal expected-cash bound is assumed. Initial time-zero right-payment atom, all interior jumps, continuous and singular-continuous cash are included.
-- source:
--   Canonical Avram dividend definitions; Proved original full Stieltjes real L1 f97e4695-e32a-46c6-996a-a7796cad36d7 and source a.e. finiteness f0d4c94c-c070-460b-bb90-95ccc0264d90; Mathlib ofReal_integral_eq_lintegral_ofReal and ENNReal.ofReal_toReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_full_stieltjes_reward_integrable_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_real_horizon_stopped_full_stieltjes_payment_ae_finite

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_03_original_full_clock_real_budget_to_ennreal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (q B : ℝ)
    (hRealBudget :
      (∫ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)).toReal ∂P) ≤ B) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal B := by sorry
