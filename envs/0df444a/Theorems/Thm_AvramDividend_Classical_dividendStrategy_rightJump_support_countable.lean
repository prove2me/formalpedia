-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable
-- name    : AvramDividend.Classical.dividendStrategy_rightJump_support_countable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:09:35.24075+00:00
-- url     : https://prove2.me/theorems/9044d9ad-758f-4608-91af-f6ff216b7b36
-- title:
--   The right dividend-payment jump times of an actual dividend strategy are countable
-- statement:
--   For every dividend strategy D and sample ω, the set of nonnegative real times at which the exact mission-defined rightLimit D differs from D itself is countable. The proof identifies the rightLimit on NNReal with the right limit of the monotone real extension, and uses the countability of the discontinuity set of a monotone real-valued function. This determines the potential support of all dividend Stieltjes measure atoms.
-- source:
--   Children monotone_rightJump_support_countable and dividendPath_real_rightLim_eq_rightLimit; formal definition IsDividendStrategy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_rightJump_support_countable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    Set.Countable {t : ℝ | 0 ≤ t ∧
      rightLimit D t.toNNReal ω ≠ D t.toNNReal ω} := by sorry
