-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_finite_cash_left_to_right_discount_error
-- name    : AvramDividend.Classical.avram_chat24_finite_cash_left_to_right_discount_error
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:09:24.890305+00:00
-- url     : https://prove2.me/theorems/16d5dc9f-5913-441d-adc8-d1328aa4e77c
-- title:
--   AvramDividend.Classical.avram_chat24_finite_cash_left_to_right_discount_error
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_finite_cash_left_to_right_discount_error from oversized parent candidate c1a8585d59e2260a34551ba02f1fc0196aa5cada2afaca89b54c9ef895880c67.
-- source:
--   candidate-decomposition:f8123fbf-cb94-45e8-aca8-e21f50ba9d61:c1a8585d59e2260a34551ba02f1fc0196aa5cada2afaca89b54c9ef895880c67

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Finset AvramDividend.Classical
open scoped NNReal ENNReal Classical

noncomputable section
theorem AvramDividend.Classical.avram_chat24_finite_cash_left_to_right_discount_error
    {ι : Type*} (s : Finset ι) (eLeft eRight d : ι → ℝ) (ε : ℝ)
    (hd : ∀ i ∈ s, 0 ≤ d i)
    (he : ∀ i ∈ s, eLeft i - eRight i ≤ ε) :
    (∑ i ∈ s, eLeft i * d i) ≤
      (∑ i ∈ s, eRight i * d i) + ε * (∑ i ∈ s, d i) := by sorry
end
