-- Prove2me | Theorems.Thm_CirclePackingConstants_n7_pattern_04_infeasible
-- name    : CirclePackingConstants.n7_pattern_04_infeasible
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T23:54:39.36276+00:00
-- url     : https://prove2.me/theorems/e19de896-31a6-4631-b149-c30486a9df08
-- title:
--   n=7 representative hole pattern (0,4) is infeasible
-- statement:
--   For the ordered occupied cells of representative hole pair (0,4), the Appendix-A strict scaled separation constraints and stated cell boxes are inconsistent.
-- source:
--   Supplied circles_in_square_n7.pdf, pp. 5–7 and Appendix A, pp. 10–12; (1,3) additionally uses the rigidity argument in §2.

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem CirclePackingConstants.n7_pattern_04_infeasible (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L : (1000:ℝ) ≤ x0) (hx0U : x0 ≤ (2000:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (1000:ℝ))
  (hx1L : (2000:ℝ) ≤ x1) (hx1U : x1 ≤ (3000:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (1000:ℝ))
  (hx2L : (0:ℝ) ≤ x2) (hx2U : x2 ≤ (1000:ℝ)) (hy2L : (1000:ℝ) ≤ y2) (hy2U : y2 ≤ (2000:ℝ))
  (hx3L : (2000:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1000:ℝ) ≤ y3) (hy3U : y3 ≤ (2000:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (1000:ℝ)) (hy4L : (2000:ℝ) ≤ y4) (hy4U : y4 ≤ (3000:ℝ))
  (hx5L : (1000:ℝ) ≤ x5) (hx5U : x5 ≤ (2000:ℝ)) (hy5L : (2000:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2000:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2000:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
  (hhT01 : (2584683:ℝ) < (x0-x1)^2+(y0-y1)^2)
  (hhT02 : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2)
  (hhT03 : (2584683:ℝ) < (x0-x3)^2+(y0-y3)^2)
  (hhT04 : (2584683:ℝ) < (x0-x4)^2+(y0-y4)^2)
  (hhT05 : (2584683:ℝ) < (x0-x5)^2+(y0-y5)^2)
  (hhT06 : (2584683:ℝ) < (x0-x6)^2+(y0-y6)^2)
  (hhT12 : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2)
  (hhT13 : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2)
  (hhT14 : (2584683:ℝ) < (x1-x4)^2+(y1-y4)^2)
  (hhT15 : (2584683:ℝ) < (x1-x5)^2+(y1-y5)^2)
  (hhT16 : (2584683:ℝ) < (x1-x6)^2+(y1-y6)^2)
  (hhT23 : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2)
  (hhT24 : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2)
  (hhT25 : (2584683:ℝ) < (x2-x5)^2+(y2-y5)^2)
  (hhT26 : (2584683:ℝ) < (x2-x6)^2+(y2-y6)^2)
  (hhT34 : (2584683:ℝ) < (x3-x4)^2+(y3-y4)^2)
  (hhT35 : (2584683:ℝ) < (x3-x5)^2+(y3-y5)^2)
  (hhT36 : (2584683:ℝ) < (x3-x6)^2+(y3-y6)^2)
  (hhT45 : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2)
  (hhT46 : (2584683:ℝ) < (x4-x6)^2+(y4-y6)^2)
  (hhT56 : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2)
  : False  := by sorry
