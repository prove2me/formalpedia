-- Prove2me | Theorems.Thm_DetDLP_D3Stopped_d3_stopped_schedule_poly
-- name    : DetDLP.D3Stopped.d3_stopped_schedule_poly
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T05:58:18.002991+00:00
-- url     : https://prove2.me/theorems/fc2ae700-550e-4710-b1f4-ab6cceda3f9a
-- title:
--   Uniform exponent bound for the stopped-core schedule
-- statement:
--   For the absolute-depth schedule with scale $S$, edge upper bound $M$, and starting depth $d_0$, the exponent appearing in the closed-schedule contraction is bounded uniformly by
--
--   $$
--   \operatorname{exponent}(s,S) \le 1028\,\frac{S}{\sqrt{\lceil\log_2 S\rceil}}
--   $$
--
--   for every $S\ge 2$. This gives a quantitative recursion budget for the stopped-core contraction interface.
-- source:
--   Deterministic Discrete Logarithms, Lemma 5.3(iii), stopped-core continuation schedule.

import Definitions.Def_DetDLP_D3StoppedSchedule
set_option autoImplicit false

namespace DetDLP.D3Stopped
open AppendixD4
theorem d3_stopped_schedule_poly (C S M d₀ : ℕ) (hS : 2 ≤ S) :
    exponent (schedule C S M d₀) S ≤ 1028*S/Real.sqrt (level S : ℝ) := by sorry
end DetDLP.D3Stopped
