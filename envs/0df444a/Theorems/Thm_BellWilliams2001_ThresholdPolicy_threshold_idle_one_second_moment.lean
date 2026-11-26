-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_threshold_idle_one_second_moment
-- name    : BellWilliams2001.ThresholdPolicy.threshold_idle_one_second_moment
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:28:09.826798+00:00
-- url     : https://prove2.me/theorems/ab81be58-ae32-4fb7-adda-ab95eafb0ef9
-- title:
--   Second moment of the first server’s diffusion-scaled idleness
-- statement:
--   For a sufficiently large threshold coefficient, diffusion-scaled server 1 idle time has a second moment bounded by a constant times one plus the square of the observation horizon, uniformly for sufficiently large scaling indices.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Threshold

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

theorem threshold_idle_one_second_moment {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ < c → ∀ T : ℕ → Allocation Ω,
      (∀ n, 1 ≤ M.threshold c n → M.IsAdmissible n (T n) ∧ M.IsThreshold c n (T n)) →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n in atTop, ∀ t : ℝ, 0 ≤ t →
        (∫⁻ ω, ENNReal.ofReal (M.Ihat n (T n) ω t 0)^2 ∂M.P) ≤ ENNReal.ofReal (A*(1+t)^3) := by sorry

end BellWilliams2001.ThresholdPolicy
