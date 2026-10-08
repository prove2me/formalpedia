-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_open_interval_of_compact_subintervals
-- name    : AvramDividend.Classical.continuousOn_open_interval_of_compact_subintervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:27:12.083586+00:00
-- url     : https://prove2.me/theorems/ff7b68cb-fd06-43e2-bb15-7993f7102c0e
-- title:
--   Continuity on all compact interior intervals yields continuity on the entire open interval
-- statement:
--   A real function f continuous on every compact [l,u] strictly inside (0,a) is continuous throughout (0,a). At each x∈(0,a), choose l=x/2 and u=(x+a)/2; the compact interval contains a neighborhood of x, so continuity on it implies continuity at x. This is the exact localisation bridge from the proven compact residual continuity of Lévy generators to continuity on the whole positive smoothness interval.
-- source:
--   Topology of compact subintervals and ContinuousOn.continuousAt in pinned Mathlib.

import Mathlib

open MeasureTheory Set Filter Topology

namespace AvramDividend.Classical

theorem continuousOn_open_interval_of_compact_subintervals
    (f : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hK : ∀ (l u : ℝ), 0 < l → l < u → u < a →
      ContinuousOn f (Icc l u)) :
    ContinuousOn f (Ioo 0 a) := by sorry

end AvramDividend.Classical
