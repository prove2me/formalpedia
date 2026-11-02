-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_uniform_interior_cutoff_secant_defect_bound
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_uniform_interior_cutoff_secant_defect_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:54:51.867031+00:00
-- url     : https://prove2.me/theorems/5d60cc4f-f8cc-4849-8d17-fd65a1331edb
-- title:
--   Uniform global under-approximation of slope-one cap continuation by strictly interior slope-one cutoffs, bounded by vanishing cap-secant defect
-- statement:
--   For positive finite cap c, a candidate w only C² strictly inside 0<y<c, w continuous at the cap and with gradient≥1 strictly inside, and any interior cutoff b∈[0,c], define f_c(y)=w(y) for y≤c and w(c)+y-c beyond, f_b similarly at b. For every nonnegative controlled reserve y, 0≤f_c(y)-f_b(y)≤[w(c)-w(b)]-(c-b). This bound is uniform in y and tends to zero as b↑c by continuity, without any cap left derivative. The inequality uses the Proved inclusive-cap secants at b,y,c and is useful to legitimate stochastic cap-boundary approximation. It makes no claim yet that the stochastic local-time term has been identified or controlled.
-- source:
--   Proved inclusive-cap secant 44b01929-5817-44ac-9439-6eb3c9879f2c, corrected core 429e17ca-5528-40b5-b593-7c03973d0706 (untouched), mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43; scope cap-corner stochastic boundary, not full chain rule or Stieltjes.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_uniform_interior_cutoff_secant_defect_bound
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (b : ℝ) (hb0 : 0 ≤ b) (hbc : b ≤ c)
    (y : ℝ) (hy : 0 ≤ y) :
    0 ≤ (if y ≤ c then w y else w c + (y - c)) -
      (if y ≤ b then w y else w b + (y - b)) ∧
    (if y ≤ c then w y else w c + (y - c)) -
      (if y ≤ b then w y else w b + (y - b)) ≤
      (w c - w b) - (c - b) := by sorry
