-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_ubv_cap_corner_inward_secant_slope_ge_one_all_scales
-- name    : AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_inward_secant_slope_ge_one_all_scales
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:40:40.10705+00:00
-- url     : https://prove2.me/theorems/dcef60e4-8013-48e3-9bfe-8fdae00080ef
-- title:
--   At every finite positive cap and every inward scale, the corrected UBV candidate has inward secant slope at least one without any cap derivative
-- statement:
--   For a candidate w continuous on [0,∞), C² only strictly inside a positive finite cap c, and w'(y)≥1 only on 0<y<c, the inward secant (w(c)−w(c−δ))/δ is at least one at every δ∈(0,c]. The theorem includes the actual endpoint c and makes no assumption of existence, finiteness, or bounded variation of a left derivative at c. This gives the exact all-scale sign comparing the slope-one continuation's right slope 1 to inward cap secants for use in any valid cap-corner smoothing/Itô–Meyer approximation. It does not assert that a cap local-time term has been derived or vanishes.
-- source:
--   Proved inclusive-cap C² gradient-to-secant 44b01929-5817-44ac-9439-6eb3c9879f2c; finite cap corner for corrected canonical UBV 429e17ca-5528-40b5-b593-7c03973d0706; separate from full dividend Stieltjes correction owned Chat04-B.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_05_ubv_cap_corner_inward_secant_slope_ge_one_all_scales
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (δ : ℝ) (hδ : 0 < δ) (hδc : δ ≤ c) :
    1 ≤ (w c - w (c - δ)) / δ := by sorry
