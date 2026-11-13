-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_initial_cash_of_global_order
-- name    : AvramDividend.Classical.avram_chat24_initial_cash_of_global_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:00:18.053653+00:00
-- url     : https://prove2.me/theorems/6f8aa274-e1dd-4131-9f05-c60b1d9356f3
-- title:
--   AvramDividend.Classical.avram_chat24_initial_cash_of_global_order
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_initial_cash_of_global_order from oversized parent candidate d06891b20bcf74e83e820d9ce7e29fcd3edb348e2a0c9ad00d47135ca4f77295.
-- source:
--   candidate-decomposition:2b85e13a-39e1-480f-b827-ab358b597b5c:d06891b20bcf74e83e820d9ce7e29fcd3edb348e2a0c9ad00d47135ca4f77295

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem AvramDividend.Classical.avram_chat24_initial_cash_of_global_order
    (w : ℝ → ℝ) (hm : MonotoneOn w (Ici 0)) (hn : ∀ y, 0 ≤ w y)
    (x : ℝ) (hx : 0 ≤ x) (δ : ℝ) (hδ : 0 ≤ δ) (d : ℝ)
    (hd : d ≤ w x - w (x - d)) : d ≤ w (x + δ) := by sorry
end
