-- Prove2me | Theorems.Thm_CirclePackingConstants_n7_rep13_interval_stage_2
-- name    : CirclePackingConstants.n7_rep13_interval_stage_2
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T00:54:34.251986+00:00
-- url     : https://prove2.me/theorems/130a9ef3-2733-456b-870c-9d4d9d0bf7cb
-- title:
--   n=7 (1,3) interval localization stage 2
-- statement:
--   One bounded Appendix-A interval-contraction stage for the $(1,3)$ representative, mapping its exact 28 endpoint state to the next endpoint state under all strict scaled separations.
-- source:
--   Supplied circles_in_square_n7.pdf, Appendix A, pp. 10–12.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem CirclePackingConstants.n7_rep13_interval_stage_2 (x0 y0 x1 y1 x2 y2 x3 y3 x4 y4 x5 y5 x6 y6 : ℝ)
  (hx0L : (0:ℝ) ≤ x0) (hx0U : x0 ≤ (775:ℝ)) (hy0L : (0:ℝ) ≤ y0) (hy0U : y0 ≤ (775:ℝ))
  (hx1L : (2000:ℝ) ≤ x1) (hx1U : x1 ≤ (2249:ℝ)) (hy1L : (0:ℝ) ≤ y1) (hy1U : y1 ≤ (163:ℝ))
  (hx2L : (1000:ℝ) ≤ x2) (hx2U : x2 ≤ (1446:ℝ)) (hy2L : (1012:ℝ) ≤ y2) (hy2U : y2 ≤ (1449:ℝ))
  (hx3L : (2751:ℝ) ≤ x3) (hx3U : x3 ≤ (3000:ℝ)) (hy3L : (1258:ℝ) ≤ y3) (hy3U : y3 ≤ (1412:ℝ))
  (hx4L : (0:ℝ) ≤ x4) (hx4U : x4 ≤ (163:ℝ)) (hy4L : (2000:ℝ) ≤ y4) (hy4U : y4 ≤ (2249:ℝ))
  (hx5L : (1258:ℝ) ≤ x5) (hx5U : x5 ≤ (1412:ℝ)) (hy5L : (2751:ℝ) ≤ y5) (hy5U : y5 ≤ (3000:ℝ))
  (hx6L : (2846:ℝ) ≤ x6) (hx6U : x6 ≤ (3000:ℝ)) (hy6L : (2846:ℝ) ≤ y6) (hy6U : y6 ≤ (3000:ℝ))
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
  : (0:ℝ) ≤ x0 ∧ x0 ≤ (712:ℝ) ∧ (0:ℝ) ≤ y0 ∧ y0 ≤ (716:ℝ) ∧ (2000:ℝ) ≤ x1 ∧ x1 ≤ (2228:ℝ) ∧ (0:ℝ) ≤ y1 ∧ y1 ≤ (152:ℝ) ∧ (1135:ℝ) ≤ x2 ∧ x2 ≤ (1424:ℝ) ∧ (1094:ℝ) ≤ y2 ∧ y2 ≤ (1416:ℝ) ∧ (2772:ℝ) ≤ x3 ∧ x3 ≤ (3000:ℝ) ∧ (1258:ℝ) ≤ y3 ∧ y3 ≤ (1409:ℝ) ∧ (0:ℝ) ≤ x4 ∧ x4 ≤ (152:ℝ) ∧ (2000:ℝ) ≤ y4 ∧ y4 ≤ (2228:ℝ) ∧ (1258:ℝ) ≤ x5 ∧ x5 ≤ (1409:ℝ) ∧ (2772:ℝ) ≤ y5 ∧ y5 ≤ (3000:ℝ) ∧ (2849:ℝ) ≤ x6 ∧ x6 ≤ (3000:ℝ) ∧ (2849:ℝ) ≤ y6 ∧ y6 ≤ (3000:ℝ)  := by sorry
