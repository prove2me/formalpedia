-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva22_original_K_local_proxy_measurable_of_cap_continuity
-- name    : AvramDividend.Classical.avram_bva22_original_K_local_proxy_measurable_of_cap_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:30:42.002194+00:00
-- url     : https://prove2.me/theorems/32e96460-d024-4618-be36-e1bb9509a521
-- title:
--   Original K stopped negative-mark kernel measurable from locally matching measurable physical reserve proxy
-- statement:
--   The exact original K time integrand uses only positive physical times strictly within the inner horizon, and therefore strictly before T. If the original prepayment reserve U agrees there with a measurable physical proxy V, and the integrated original mark kernel ψ is continuous on the actual closed reserve cap, then the cap-masked ψ∘V is measurable by the Proved closed-cap piecewise theorem 2a89ef26. Multiplying by the continuous discount and applying the measurable time/ruin mask yields measurability of the exact original K integrand. This directly combines the no-jump source U proxy, finite mark continuity and K real-time bridge for 7ccc2a1a.
-- source:
--   Source-K measurable discounted negative mark kernel from zero-jump physical reserve proxy and cap-continuous mark rate, necessary for original 7ccc2a1a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva21_closed_cap_continuous_kernel_mask_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva22_original_K_local_proxy_measurable_of_cap_continuity
    (C τ : ℝ≥0∞) (q T : ℝ) (hT : 0 < T) (n : ℕ)
    (U V : ℝ≥0 → ℝ) (hV : Measurable V)
    (hUV : ∀ t : ℝ≥0, 0 < t → (t : ℝ) < T → U t = V t)
    (ψ : ℝ → ℝ)
    (hψ : ContinuousOn ψ {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}) :
    Measurable (fun t : ℝ≥0 =>
      if 0 < t ∧ (t : ℝ) < T - T / ((n : ℝ) + 2) ∧
         (t : ℝ≥0∞) ≤ τ ∧
         0 ≤ U t ∧ ENNReal.ofReal (U t) ≤ C
      then Real.exp (-(q * (t : ℝ))) * ψ (U t)
      else 0) := by sorry
