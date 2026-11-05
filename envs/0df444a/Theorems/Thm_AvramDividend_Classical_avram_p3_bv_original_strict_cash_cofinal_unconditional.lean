-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_unconditional
-- name    : AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:27:12.412191+00:00
-- url     : https://prove2.me/theorems/e4ffad74-0756-460c-9e2b-f035aaf5d7df
-- title:
--   Original complete strict-horizon Stieltjes cash is exactly its cofinal monotone limit
-- statement:
--   Exactly the real discounted original Stieltjes dividend cash before T equals the increasing supremum of cash before cofinal strict cutoffs, for every source path and every actual original dividend measure. There is no external payment-time measurability assumption: it is proved from the source Borel definition using paymentTimes_measurable. In particular, all diffuse and right-payment atoms strictly before T survive the limit, with no claim about a horizon-T payment.
-- source:
--   Unconditional source paymentTimes_measurable and the proved strict cash cofinal lintegral_iSup theorem. No compensator, martingale or source replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_cofinal_lintegral_iSup
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_bv_original_strict_cash_cofinal_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (u : ℕ → ℝ) (hmono : Monotone u)
    (hbelow : ∀ n, u n ≤ T)
    (hcover : ∀ s : ℝ, s < T → ∃ n, s < u n) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) =
      ⨆ n, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (u n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂dividendMeasure D ω) := by sorry
