-- Prove2me | Theorems.Thm_ChatterjeeSamuelson_UniformEfficiency_total_profit_max_calculus
-- name    : ChatterjeeSamuelson.UniformEfficiency.total_profit_max_calculus
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-01T10:41:42.062277+00:00
-- url     : https://prove2.me/theorems/b8aabda7-44cd-4b2f-8506-58252c5fb252
-- title:
--   Example 1(c)(iii) optimization: total profit max of (9/64)vbar at k = 1/2
-- statement:
--   For vbar > 0, the function k |-> (vbar/16)(1+k)(2-k) attains its maximum over [0,1] at k = 1/2, where it equals (9/64)vbar.

import Mathlib

open Set

namespace ChatterjeeSamuelson.UniformEfficiency

/-- Example 1(c)(iii), optimization part (Chatterjee & Samuelson, *Bargaining under
Incomplete Information*, Oper. Res. 31(5) 1983, §3, p. 842 [PDF 8]: "π_s + π_b =
(v̄/16)(1 + k)(2 − k), which has a maximum of (9/64)v̄, at k = ½").

The map κ ↦ (v̄/16)(1 + κ)(2 − κ) attains its maximum over κ ∈ [0, 1] at κ = 1/2,
where it equals (9/64)v̄. Pure calculus: (1 + κ)(2 − κ) = 9/4 − (κ − 1/2)². -/
theorem total_profit_max_calculus (vbar : ℝ) (hv : 0 < vbar) :
    IsMaxOn (fun κ : ℝ => vbar / 16 * (1 + κ) * (2 - κ)) (Icc 0 1) (1 / 2) ∧
      vbar / 16 * (1 + 1 / 2) * (2 - 1 / 2) = 9 / 64 * vbar := by sorry

end ChatterjeeSamuelson.UniformEfficiency
