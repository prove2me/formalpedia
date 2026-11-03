-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_actual_path_cash_requires_strict_positive_horizon
-- name    : AvramDividend.Classical.avram_wave7_09_bv_zero_cap_actual_path_cash_requires_strict_positive_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:45:12.359137+00:00
-- url     : https://prove2.me/theorems/2beae171-5e8e-46ab-a2cd-333ea7d8648d
-- title:
--   Positive original BV zero-cap sample cash occurs at a strictly positive finite horizon
-- statement:
--   For every original Standing finite-jump-activity bounded-variation Lévy process and positive discount q, there exists a real path ω in the actual given sample space and a natural horizon n>0 whose own stopped full Stieltjes dividend payout under the original cap-zero zero-barrier strategy is positive. The Proved actual sample path witness 70c63725 is strengthened using Proved zero-horizon exact pathwise cash zero c96bf020 and original source barrier admissibility 32b4ccb8. No replacement probability model is used.
-- source:
--   Original exact Ω, P, 𝓕, X and complete right-atom Stieltjes definition; Proved 70c63725, c96bf020, 32b4ccb8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_09_bv_zero_cap_actual_path_cash_requires_strict_positive_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ (n : ℕ) (ω : Ω), 0 < n ∧
      0 < (∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω)) := by sorry
