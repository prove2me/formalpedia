-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a259_one_sided_global_HJB_endpoint_exponential_Gaussian_increment
-- name    : AvramDividend.Classical.avram_ga_a259_one_sided_global_HJB_endpoint_exponential_Gaussian_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:49:35.06113+00:00
-- url     : https://prove2.me/theorems/24ee1fa7-8654-4862-80c0-036b74f9dde2
-- title:
--   Positive original Gaussian postincrement endpoint bounded by compact-start exponential times raw Gaussian increment exponential
-- statement:
--   Suppose the value w has a one-sided global positive-reserve exponential upper bound. Then for every true Gaussian physical-cell start reserve y≤b and any raw increment r with strictly positive postincrement endpoint y+r, the endpoint value is bounded by K exp(theta b) exp(theta r). This avoids requiring a fixed positive lower bound on the endpoint and allows the original positive Gaussian exponential-tail a233 to control large postpayment source contributions.
-- source:
--   Global original HJB positive reserve upper a257 and original Gaussian raw positive exp expected tails a233.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a259_one_sided_global_HJB_endpoint_exponential_Gaussian_increment
    (w : ℝ → ℝ) (K theta b y r : ℝ)
    (hK : 0 ≤ K) (hθ : 0 ≤ theta)
    (hy : y ≤ b) (hEnd : 0 < y+r)
    (hw : ∀ t : ℝ, 0 < t → w t ≤ K*Real.exp (theta*t)) :
    w (y+r) ≤
      (K*Real.exp (theta*b))*Real.exp (theta*r) := by sorry
