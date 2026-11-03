-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_inclusive_ruin_predictable_strict_hjb_interior
-- name    : AvramDividend.Classical.avram_wave7_17_original_inclusive_ruin_predictable_strict_hjb_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:35:04.564146+00:00
-- url     : https://prove2.me/theorems/4e14265e-2318-4e28-82e2-83814969ad15
-- title:
--   Genuine original inclusive ruin-stopped strict HJB interior is predictable for the source right-continuous filtration
-- statement:
--   The actual controlled Lévy predictable pre-payment reserve and the inclusive survival indicator t≤ruinTime are strongly predictable for the original right-continuous filtration. Thus their strict positive reserve and strict sub-cap intersection through the inclusive ruin time is a measurable set for the original predictable sigma algebra. The inclusive ruin instant is essential for source jumps at inaccessible ruin times; the strict pre-ruin support t<ruinTime need not itself be predictable. This is the exact localisation support needed to pass actual HJB generator and negative-mark compensation into a predictable source clock. The theorem assumes no alternative sample space, Poisson copy, HJB sign, integrability or cash-budget conclusion.
-- source:
--   Original dividend-controlled spectrally negative Lévy process; Proved controlled reserve strong predictability 94ee9994, Proved original inclusive survival predictability 69806d16, Proved original ruin stopping time 2d036d4f. The inclusive stop differs from strict paymentTimes at an inaccessible ruin source jump, which requires separate source-jump handling.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_inclusive_ruin_predictable_strict_hjb_interior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) :
    MeasurableSet[𝓕.rightCont.predictable]
      {p : ℝ≥0 × Ω |
        (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C} := by sorry
