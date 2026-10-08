-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_of_continuousOn_each_compact_Icc
-- name    : AvramDividend.Classical.continuousOn_of_continuousOn_each_compact_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T10:54:45.009655+00:00
-- url     : https://prove2.me/theorems/1974fca7-8c43-4efb-910c-f4ea74b31d20
-- title:
--   Continuity on every compact subinterval implies continuity on a positive open interval
-- statement:
--   A real function continuous on every compact [l,u] strictly inside (0,a) is continuous on the open interval. For any x take [x/2,(x+a)/2], which contains x in its interior. This globalises the previously verified local compact continuity of the Lévy generator residual without invoking global differentiability.
-- source:
--   Pinned Mathlib neighbourhood, support and compact interval continuity theorems; Avram Dividend generator residual localisation.

import Mathlib

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem continuousOn_of_continuousOn_each_compact_Icc
    (f : ℝ → ℝ) (a : ℝ)
    (hcompact : ∀ l u : ℝ, 0 < l → l < u → u < a →
      ContinuousOn f (Icc l u)) :
    ContinuousOn f (Ioo 0 a) := by sorry

end AvramDividend.Classical
