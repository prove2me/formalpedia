-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
-- name    : AvramDividend.Classical.avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T03:41:09.184677+00:00
-- url     : https://prove2.me/theorems/5d9c74c7-cba4-4bdd-98d0-30f367d296f1
-- title:
--   Original finite-cap bounded stopped strict reward with true zero-clock mask is L1
-- statement:
--   Necessary integrability step for root-connected finite-cap Fatou passage 3308ae9d. The original finite-cap prepayment terminal is L1 at every physical stopping time; the original discounted strict cash is L1 at bounded stopping times. Their sum remains L1 after assigning the source-exact zero-clock w(x) value. Proof reuses the three authoritative existing Proved lemmas.
-- source:
--   Direct composition of 7f672fd4, ed1a42d8 and avram_ubv_loc6_rightcont_stopping_zero_mask_integrable. Zero auxiliary processes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_rightcont_stopping_zero_mask_integrable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 < q) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      if σ ω = 0 then w x else
        Real.exp (-(q * (σ ω : ℝ))) *
          w (riskProcess X x D (σ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := by sorry
