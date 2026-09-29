-- Prove2me | Theorems.Thm_CirclePackingConstants_n7_pattern_17_root_hi_0_stage
-- name    : CirclePackingConstants.n7_pattern_17_root_hi_0_stage
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-27T01:26:25.284987+00:00
-- url     : https://prove2.me/theorems/4c5d98ff-dfb2-4769-9d43-ed59ea481432
-- title:
--   n=7 (1,7) staged verifier transition n7_root_hi_0
-- statement:
--   Exact bounded endpoint-state transition from the Appendix-A verifier for the $(1,7)$ representative.
-- source:
--   Supplied circles_in_square_n7.pdf, Appendix A, pp. 10–12.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem CirclePackingConstants.n7_pattern_17_root_hi_0_stage (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
 (hx0L:(0:ℝ)≤x0 ) (hx0U:x0≤(1000:ℝ) ) (hy0L:(0:ℝ)≤y0 ) (hy0U:y0≤(484:ℝ))
 (hx1L:(2000:ℝ)≤x1 ) (hx1U:x1≤(3000:ℝ) ) (hy1L:(0:ℝ)≤y1 ) (hy1U:y1≤(484:ℝ))
 (hx2L:(0:ℝ)≤x2 ) (hx2U:x2≤(148:ℝ) ) (hy2L:(1258:ℝ)≤y2 ) (hy2U:y2≤(1742:ℝ))
 (hx3L:(1426:ℝ)≤x3 ) (hx3U:x3≤(1574:ℝ) ) (hy3L:(1000:ℝ)≤y3 ) (hy3U:y3≤(2000:ℝ))
 (hx4L:(2852:ℝ)≤x4 ) (hx4U:x4≤(3000:ℝ) ) (hy4L:(1258:ℝ)≤y4 ) (hy4U:y4≤(1742:ℝ))
 (hx5L:(0:ℝ)≤x5 ) (hx5U:x5≤(1000:ℝ) ) (hy5L:(2516:ℝ)≤y5 ) (hy5U:y5≤(3000:ℝ))
 (hx6L:(2500:ℝ)≤x6 ) (hx6U:x6≤(3000:ℝ) ) (hy6L:(2516:ℝ)≤y6 ) (hy6U:y6≤(3000:ℝ))
 (hT01:(2584683:ℝ)<(x0-x1)^2+(y0-y1)^2)
 (hT02:(2584683:ℝ)<(x0-x2)^2+(y0-y2)^2)
 (hT03:(2584683:ℝ)<(x0-x3)^2+(y0-y3)^2)
 (hT04:(2584683:ℝ)<(x0-x4)^2+(y0-y4)^2)
 (hT05:(2584683:ℝ)<(x0-x5)^2+(y0-y5)^2)
 (hT06:(2584683:ℝ)<(x0-x6)^2+(y0-y6)^2)
 (hT12:(2584683:ℝ)<(x1-x2)^2+(y1-y2)^2)
 (hT13:(2584683:ℝ)<(x1-x3)^2+(y1-y3)^2)
 (hT14:(2584683:ℝ)<(x1-x4)^2+(y1-y4)^2)
 (hT15:(2584683:ℝ)<(x1-x5)^2+(y1-y5)^2)
 (hT16:(2584683:ℝ)<(x1-x6)^2+(y1-y6)^2)
 (hT23:(2584683:ℝ)<(x2-x3)^2+(y2-y3)^2)
 (hT24:(2584683:ℝ)<(x2-x4)^2+(y2-y4)^2)
 (hT25:(2584683:ℝ)<(x2-x5)^2+(y2-y5)^2)
 (hT26:(2584683:ℝ)<(x2-x6)^2+(y2-y6)^2)
 (hT34:(2584683:ℝ)<(x3-x4)^2+(y3-y4)^2)
 (hT35:(2584683:ℝ)<(x3-x5)^2+(y3-y5)^2)
 (hT36:(2584683:ℝ)<(x3-x6)^2+(y3-y6)^2)
 (hT45:(2584683:ℝ)<(x4-x5)^2+(y4-y5)^2)
 (hT46:(2584683:ℝ)<(x4-x6)^2+(y4-y6)^2)
 (hT56:(2584683:ℝ)<(x5-x6)^2+(y5-y6)^2)
 : (0:ℝ)≤x0 ∧ x0≤(790:ℝ) ∧ (0:ℝ)≤y0 ∧ y0≤(212:ℝ) ∧ (2000:ℝ)≤x1 ∧ x1≤(2345:ℝ) ∧ (0:ℝ)≤y1 ∧ y1≤(210:ℝ) ∧ (0:ℝ)≤x2 ∧ x2≤(83:ℝ) ∧ (1400:ℝ)≤y2 ∧ y2≤(1478:ℝ) ∧ (1491:ℝ)≤x3 ∧ x3≤(1574:ℝ) ∧ (1812:ℝ)≤y3 ∧ y3≤(2000:ℝ) ∧ (2917:ℝ)≤x4 ∧ x4≤(3000:ℝ) ∧ (1258:ℝ)≤y4 ∧ y4≤(1468:ℝ) ∧ (0:ℝ)≤x5 ∧ x5≤(516:ℝ) ∧ (2769:ℝ)≤y5 ∧ y5≤(3000:ℝ) ∧ (2541:ℝ)≤x6 ∧ x6≤(3000:ℝ) ∧ (2798:ℝ)≤y6 ∧ y6≤(3000:ℝ)  := by sorry
