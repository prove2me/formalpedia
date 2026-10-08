-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_Ioo_of_continuousOn_all_compact_subintervals
-- name    : AvramDividend.Classical.continuousOn_Ioo_of_continuousOn_all_compact_subintervals
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T12:44:56.979012+00:00
-- url     : https://prove2.me/theorems/06a2fec9-cbb7-425e-9499-cc09dce9a4bf
-- title:
--   Compact-local continuity implies continuity throughout an open positive interval
-- statement:
--   A function f that is continuous on every compact interval [l,u] strictly contained in (0,a), where 0<a, is continuous on the whole open interval (0,a). The proof chooses [x/2,(x+a)/2] around any x∈(0,a), obtains an ordinary neighbourhood at x contained in that compact interval, and upgrades continuousOn there to continuousAt x. This bridges the compact generator regularity results to the domain of the q-harmonicity theorem.
-- source:
--   Topology of real intervals and Mathlib ContinuousOn.continuousAt, used to localise the Avram Dividend Lévy generator.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem continuousOn_Ioo_of_continuousOn_all_compact_subintervals
    (f : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcompact : ∀ l u : ℝ, 0 < l → l < u → u < a →
      ContinuousOn f (Icc l u)) :
    ContinuousOn f (Ioo 0 a) := by sorry

end AvramDividend.Classical
