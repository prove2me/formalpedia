-- Prove2me | Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_5
-- name    : CirclePackingConstants.n7_rep13_interval_stage_5
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T00:54:38.731986+00:00
-- url     : https://prove2.me/theorems/1a568d2e-dbc7-4349-ac93-bde79570e6f3
-- title:
--   n=7 (1,3) interval localization stage 5
-- statement:
--   One bounded Appendix-A interval-contraction stage for the $(1,3)$ representative, mapping its exact 28 endpoint state to the next endpoint state under all strict scaled separations.
-- source:
--   Supplied circles_in_square_n7.pdf, Appendix A, pp. 10–12.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem CirclePackingConstants.n7_rep13_interval_stage_5 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L : (0:ℝ) ≤ x0) (hx0U : x0 ≤ (602:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (604:ℝ))
  (hx1L : (2122:ℝ) ≤ x1) (hx1U : x1 ≤ (2203:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (50:ℝ))
  (hx2L : (1325:ℝ) ≤ x2) (hx2U : x2 ≤ (1399:ℝ)) (hy2L : (1314:ℝ) ≤ y2) (hy2U : y2 ≤ (1396:ℝ))
  (hx3L : (2930:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1316:ℝ) ≤ y3) (hy3U : y3 ≤ (1396:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (63:ℝ)) (hy4L : (2106:ℝ) ≤ y4) (hy4U : y4 ≤ (2208:ℝ))
  (hx5L : (1336:ℝ) ≤ x5) (hx5U : x5 ≤ (1399:ℝ)) (hy5L : (2918:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2941:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2920:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
  (hT01 : (2584683:ℝ) < (x0-x1)^2+(y0-y1)^2)
  (hT02 : (2584683:ℝ) < (x0-x2)^2+(y0-y2)^2)
  (hT03 : (2584683:ℝ) < (x0-x3)^2+(y0-y3)^2)
  (hT04 : (2584683:ℝ) < (x0-x4)^2+(y0-y4)^2)
  (hT05 : (2584683:ℝ) < (x0-x5)^2+(y0-y5)^2)
  (hT06 : (2584683:ℝ) < (x0-x6)^2+(y0-y6)^2)
  (hT12 : (2584683:ℝ) < (x1-x2)^2+(y1-y2)^2)
  (hT13 : (2584683:ℝ) < (x1-x3)^2+(y1-y3)^2)
  (hT14 : (2584683:ℝ) < (x1-x4)^2+(y1-y4)^2)
  (hT15 : (2584683:ℝ) < (x1-x5)^2+(y1-y5)^2)
  (hT16 : (2584683:ℝ) < (x1-x6)^2+(y1-y6)^2)
  (hT23 : (2584683:ℝ) < (x2-x3)^2+(y2-y3)^2)
  (hT24 : (2584683:ℝ) < (x2-x4)^2+(y2-y4)^2)
  (hT25 : (2584683:ℝ) < (x2-x5)^2+(y2-y5)^2)
  (hT26 : (2584683:ℝ) < (x2-x6)^2+(y2-y6)^2)
  (hT34 : (2584683:ℝ) < (x3-x4)^2+(y3-y4)^2)
  (hT35 : (2584683:ℝ) < (x3-x5)^2+(y3-y5)^2)
  (hT36 : (2584683:ℝ) < (x3-x6)^2+(y3-y6)^2)
  (hT45 : (2584683:ℝ) < (x4-x5)^2+(y4-y5)^2)
  (hT46 : (2584683:ℝ) < (x4-x6)^2+(y4-y6)^2)
  (hT56 : (2584683:ℝ) < (x5-x6)^2+(y5-y6)^2)
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (595:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (595:ℝ) ∧ (2157:ℝ) ≤ x1 ∧ x1 ≤ (2200:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (26:ℝ) ∧ (1370:ℝ) ≤ x2 ∧ x2 ≤ (1394:ℝ) ∧ (1368:ℝ) ≤ y2 ∧ y2 ≤ (1393:ℝ) ∧ (2977:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1368:ℝ) ≤ y3 ∧ y3 ≤ (1393:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (20:ℝ) ∧ (2168:ℝ) ≤ y4 ∧ y4 ≤ (2201:ℝ) ∧ (1361:ℝ) ≤ x5 ∧ x5 ≤ (1395:ℝ) ∧ (2975:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2967:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2952:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ)  := by sorry
