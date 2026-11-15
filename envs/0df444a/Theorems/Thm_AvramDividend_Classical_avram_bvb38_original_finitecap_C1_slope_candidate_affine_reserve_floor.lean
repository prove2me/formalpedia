-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb38_original_finitecap_C1_slope_candidate_affine_reserve_floor
-- name    : AvramDividend.Classical.avram_bvb38_original_finitecap_C1_slope_candidate_affine_reserve_floor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:21:46.603039+00:00
-- url     : https://prove2.me/theorems/0f8f3bc8-c0ba-4599-9080-b23fd44f396e
-- title:
--   Original finite-cap C1 slope condition forces candidate value at reserve y above w(0)+y
-- statement:
--   For a genuine finite reserve cap C>0 and original continuous candidate w with C1 interior and derivative at least one on 0<y<C, prove w(y)≥w(0)+y at EVERY closed-band reserve y in [0,C]. This supplies the exact deterministic positive payoff reserve floor at zero, interior and cap to justify original stopped HJB terminal and cash contact arguments. Deduce directly from the already Proved original finite-cap global secant theorem 849da3fc.
-- source:
--   Proved 849da3fc avram_p3_bv_finite_cap_linear_global_secant, same original C1 candidate and cap, no stochastic assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb38_original_finitecap_C1_slope_candidate_affine_reserve_floor
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal →
      w 0 + y ≤ w y := by sorry
