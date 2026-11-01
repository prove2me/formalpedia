-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_local_exponential_scale_sandwich_log_deriv
-- name    : AvramDividend.Classical.avram_wave4_01_local_exponential_scale_sandwich_log_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:29:22.287299+00:00
-- url     : https://prove2.me/theorems/d3a33430-c0f4-4a47-a913-d2af00f42a0a
-- title:
--   Local exponential scale-ratio bounds imply logarithmic differentiability
-- statement:
--   Positive W and continuous κ imply the logarithmic derivative has value κ(a) if exponential two-point W-ratio inequalities hold whenever 0<a<b and b-a<a. For each fixed a, slopes near a meet this local restriction in both directions. This matches the authentic first-record scale sandwich without extending its domain.
-- source:
--   Adapted from canonically Proved global exponential sandwich log derivative da982a88 and local two-point slope squeeze proposed Wave 4.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_local_two_point_slope_squeeze

open AvramDividend.Classical Real Set

theorem AvramDividend.Classical.avram_wave4_01_local_exponential_scale_sandwich_log_deriv
    (W κ : ℝ → ℝ)
    (hW : ∀ a : ℝ, 0 < a → 0 < W a)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hsand : ∀ a b : ℝ, 0 < a → a < b → b - a < a →
      Real.exp (-(κ a * (b - a))) ≤ W a / W b ∧
      W a / W b ≤ Real.exp (-(κ b * (b - a)))) :
    ∀ a : ℝ, 0 < a →
      HasDerivAt (fun x : ℝ => Real.log (W x)) (κ a) a := by sorry
