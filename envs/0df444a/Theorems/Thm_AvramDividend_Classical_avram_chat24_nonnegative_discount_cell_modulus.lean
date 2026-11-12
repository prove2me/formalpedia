-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_nonnegative_discount_cell_modulus
-- name    : AvramDividend.Classical.avram_chat24_nonnegative_discount_cell_modulus
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:08:46.121768+00:00
-- url     : https://prove2.me/theorems/48c5519a-4916-4def-87b6-434d93438e79
-- title:
--   AvramDividend.Classical.avram_chat24_nonnegative_discount_cell_modulus
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_nonnegative_discount_cell_modulus from oversized parent candidate c1a8585d59e2260a34551ba02f1fc0196aa5cada2afaca89b54c9ef895880c67.
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
theorem AvramDividend.Classical.avram_chat24_nonnegative_discount_cell_modulus
    (q a b h : ℝ) (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) (hwidth : b - a ≤ h) :
    Real.exp (-(q * a)) - Real.exp (-(q * b)) ≤ q * h := by sorry
end
