-- Prove2me | Theorems.Thm_CirclePackingConstants_n7_pattern_17_low_high_infeasible
-- name    : CirclePackingConstants.n7_pattern_17_low_high_infeasible
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T00:48:34.116082+00:00
-- url     : https://prove2.me/theorems/66f6e1a8-d7fe-4da5-9868-3c18fe78a982
-- title:
--   n=7 (1,7) low/high verifier leaf is infeasible
-- statement:
--   The specified closed split branch of the $(1,7)$ representative verifier is inconsistent with the strict scaled separations.
-- source:
--   Supplied circles_in_square_n7.pdf, Appendix A, pp. 10–12.

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem CirclePackingConstants.n7_pattern_17_low_high_infeasible (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L:(0:ℝ)≤x0) (hx0U:x0≤(1000:ℝ)) (hy0L:(0:ℝ)≤y0) (hy0U:y0≤(1000:ℝ))
  (hx1L:(2000:ℝ)≤x1) (hx1U:x1≤(3000:ℝ)) (hy1L:(0:ℝ)≤y1) (hy1U:y1≤(1000:ℝ))
  (hx2L:(0:ℝ)≤x2) (hx2U:x2≤(1000:ℝ)) (hy2L:(1000:ℝ)≤y2) (hy2U:y2≤(2000:ℝ))
  (hx3L:(1000:ℝ)≤x3) (hx3U:x3≤(2000:ℝ)) (hy3L:(1000:ℝ)≤y3) (hy3U:y3≤(2000:ℝ))
  (hx4L:(2000:ℝ)≤x4) (hx4U:x4≤(3000:ℝ)) (hy4L:(1000:ℝ)≤y4) (hy4U:y4≤(2000:ℝ))
  (hx5L:(0:ℝ)≤x5) (hx5U:x5≤(1000:ℝ)) (hy5L:(2000:ℝ)≤y5) (hy5U:y5≤(3000:ℝ))
  (hx6L:(2000:ℝ)≤x6) (hx6U:x6≤(3000:ℝ)) (hy6L:(2000:ℝ)≤y6) (hy6U:y6≤(3000:ℝ))
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
  (hsplit0 : x6 ≤ (2500:ℝ))
  (hsplit1 : (2500:ℝ) ≤ x1)
  : False  := by sorry
