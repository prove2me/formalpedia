-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gauss_finitec2_cap_quadratic_glue
-- name    : AvramDividend.Classical.avram_gauss_finitec2_cap_quadratic_glue
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T00:41:43.395302+00:00
-- url     : https://prove2.me/theorems/4745a3db-5292-41af-bede-e98648fc728b
-- title:
--   Global one-sided quadratic estimate across a Gaussian dividend cap
-- statement:
--   Given the original C2 interior one-sided quadratic Taylor estimate on the finite top-cap band, the original HJB gradient lower bound, and the monotonicity of value minus reserve to the cap, the cap-linear extension admits a single quadratic upper bound for all states and destinations above the band floor. This includes a starting state exactly at the cap and overshoot across the cap, without requiring w differentiable at the cap or a local-time term. Needed in original physical stopped Gaussian Ito grid for d1caa4aa.
-- source:
--   CAP-Q cap-contact gluing in GAUSS-FINITE-C2 plan; direct necessary finite-cap original-X/D stopped C2 Ito-to-Stieltjes proof child d1caa4aa, after proved uniform gradient cap ODE f80bc7ac.

import Mathlib.Analysis.Convex.Deriv

open Set
noncomputable section

theorem AvramDividend.Classical.avram_gauss_finitec2_cap_quadratic_glue
    (w : ℝ → ℝ) (u C L : ℝ) (huC : u < C) (hL : 0 ≤ L)
    (hgrad : ∀ s ∈ Ico u C, 1 ≤ deriv w s)
    (hquad : ∀ s ∈ Ico u C, ∀ t ∈ Icc u C,
      w t ≤ w s + deriv w s * (t - s) + L / 2 * (t - s) ^ 2)
    (hgrowth : ∀ t ∈ Icc u C, C - t ≤ w C - w t) :
    let V : ℝ → ℝ := fun y => if y ≤ C then w y else w C + (y - C)
    let g : ℝ → ℝ := fun y => if y < C then deriv w y else 1
    ∀ s t : ℝ, u ≤ s → u ≤ t →
      V t ≤ V s + g s * (t - s) + L / 2 * (t - s) ^ 2 := by sorry
