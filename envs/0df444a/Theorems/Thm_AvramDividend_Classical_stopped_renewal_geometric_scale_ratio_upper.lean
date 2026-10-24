-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_renewal_geometric_scale_ratio_upper
-- name    : AvramDividend.Classical.stopped_renewal_geometric_scale_ratio_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T20:52:04.789703+00:00
-- url     : https://prove2.me/theorems/8ab7d463-8ad0-480c-8509-797a9e329821
-- title:
--   Forward scale ratio geometric renewal identity
-- statement:
--   The forward scale ratio p=W(a)/W(a+ε) yields the upper finite-difference reward ε/(1−p) by algebra, provided the scale values and increment are nonzero. This supplies the exact final rewrite in the stopped renewal upper-bound derivation.
-- source:
--   Avram Dividend stopped-renewal finite-difference bounds and geometric first-record reward reduction.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem AvramDividend.Classical.stopped_renewal_geometric_scale_ratio_upper
  (W : ℝ → ℝ) (a ε : ℝ)
  (hWa : W (a + ε) ≠ 0)
  (hgap : W (a + ε) - W a ≠ 0) :
  ε / (1 - W a / W (a + ε)) =
    ε * W (a + ε) / (W (a + ε) - W a) := by sorry
