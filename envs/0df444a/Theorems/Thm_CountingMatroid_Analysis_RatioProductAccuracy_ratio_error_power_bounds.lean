-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_RatioProductAccuracy_ratio_error_power_bounds
-- name    : CountingMatroid.Analysis.RatioProductAccuracy.ratio_error_power_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T15:44:25.621643+00:00
-- url     : https://prove2.me/theorems/d10dfd1c-095b-4055-a317-cf53d773c344
-- title:
--   Power bounds for accumulated ratio errors
-- statement:
--   Let $L\in\mathbb N$ and let $\varepsilon\in\mathbb Q$ satisfy $0<\varepsilon<1$. Put $$\eta=\frac{\varepsilon}{32(L+1)}.$$ Then $$1-\frac{\varepsilon}{4}\le\left(\frac{1-\eta}{1+\eta}\right)^L,\qquad\left(\frac{1+\eta}{1-\eta}\right)^L\le1+\frac{\varepsilon}{4}.$$
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/RatioProductAccuracy.lean#L10-L51

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
set_option autoImplicit false

namespace CountingMatroid.Analysis.RatioProductAccuracy
end CountingMatroid.Analysis.RatioProductAccuracy
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.RatioProductAccuracy

theorem CountingMatroid.Analysis.RatioProductAccuracy.ratio_error_power_bounds (L : ℕ) (ε : ℚ)
    (hε : 0 < ε) (hεone : ε < 1) :
    let η := ε / (32 * ((L : ℚ) + 1))
    1 - ε / 4 ≤ ((1 - η) / (1 + η)) ^ L ∧
      ((1 + η) / (1 - η)) ^ L ≤ 1 + ε / 4 := by sorry
