-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_C1_positive_gradient_global_order
-- name    : AvramDividend.Classical.avram_chat24_C1_positive_gradient_global_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T07:46:43.037834+00:00
-- url     : https://prove2.me/theorems/4fce9eec-fb5d-4c8e-9767-9db80878fffe
-- title:
--   AvramDividend.Classical.avram_chat24_C1_positive_gradient_global_order
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_C1_positive_gradient_global_order from oversized parent candidate 5940103aa8f0e8bdc97da81da2bdf328fe609610498964dfa67cfb728c6f4298.
-- source:
--   candidate-decomposition:2b85e13a-39e1-480f-b827-ab358b597b5c:5940103aa8f0e8bdc97da81da2bdf328fe609610498964dfa67cfb728c6f4298

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem AvramDividend.Classical.avram_chat24_C1_positive_gradient_global_order
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0) (hs : ContDiffOn ℝ 1 w (Ioi 0))
    (hg : ∀ y > 0, 1 ≤ deriv w y) :
    MonotoneOn w (Ici 0) ∧ ∀ y : ℝ, 0 ≤ w y := by sorry
end
