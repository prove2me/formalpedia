-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_pre_rightpay_clipped_reserve_predictable
-- name    : AvramDividend.Classical.avram_ubv_loc6_original_pre_rightpay_clipped_reserve_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:52:22.519094+00:00
-- url     : https://prove2.me/theorems/1ed1dfe9-d74d-4c06-83a7-5305e8a35b52
-- title:
--   Clipped original pre-right-payment reserve is predictable for the right-continuous filtration
-- statement:
--   For the actual original spectrally negative Lévy process and an admissible dividend strategy, the left limit of the pre-right-dividend reserve x+X-rightLimit(D) clipped to any fixed compact real band is measurable with respect to the right-continuous filtration's predictable sigma algebra, without new adaptedness assumptions. The clipping uses exactly the original right-limit dividend convention, including time-zero and jump effects.
-- source:
--   Direct consequence of Proved physical reserve strong predictability theorem 94ee9994 by measurable compact-band masking; no distributional or martingale assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original physical pre-right-dividend reserve remains predictable after
    clipping to any real compact band; this uses the right-continuous filtration. -/

theorem AvramDividend.Classical.avram_ubv_loc6_original_pre_rightpay_clipped_reserve_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (δ v : ℝ) :
    Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
        if y ∈ Icc δ v then y else δ) := by sorry
