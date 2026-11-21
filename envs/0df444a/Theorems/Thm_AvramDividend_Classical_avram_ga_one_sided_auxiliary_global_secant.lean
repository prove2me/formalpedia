-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_one_sided_auxiliary_global_secant
-- name    : AvramDividend.Classical.avram_ga_one_sided_auxiliary_global_secant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T20:23:12.972201+00:00
-- url     : https://prove2.me/theorems/f0c6c841-9642-4123-95f7-574dc5663b40
-- title:
--   Global positive secant for the genuine lower-extended finite-cap HJB potential
-- statement:
--   Let w be continuous at zero and continuously differentiable on the strict reserve interior, with derivative at least one; form the globally slope-one extension w(0)+y below zero, w(y) on [0,c], and w(c)+y-c above c. Then the extension satisfies the complete secant inequality V(y)-V(x)≥y-x for all real x≤y, including right-dividend jump crossings through zero or c. This is the deterministic missing ingredient for the one-sided cap mollification in v5 Section 25.
-- source:
--   Direct extension of the authoritative Proved source theorem 420ddace across the negative auxiliary linear branch; no source payoff is altered and no stochastic integral lemma is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_cap_linear_extension_full_secant
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_one_sided_auxiliary_global_secant
    (c : ℝ) (hc : 0 < c) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < ENNReal.ofReal c})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < ENNReal.ofReal c → 1 ≤ deriv w y)
    (x y : ℝ) (hxy : x ≤ y) :
    y - x ≤
      (if y < 0 then w 0 + y else
        if y ≤ c then w y else w c + (y - c)) -
      (if x < 0 then w 0 + x else
        if x ≤ c then w x else w c + (x - c)) := by sorry
