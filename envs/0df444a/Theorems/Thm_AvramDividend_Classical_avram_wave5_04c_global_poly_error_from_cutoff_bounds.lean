-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_global_poly_error_from_cutoff_bounds
-- name    : AvramDividend.Classical.avram_wave5_04c_global_poly_error_from_cutoff_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:19:07.508919+00:00
-- url     : https://prove2.me/theorems/3c829bf9-0814-4728-b1c4-6a7a33b555e9
-- title:
--   Global negative jump polynomial error from weighted compact cutoff envelope
-- statement:
--   Combines a global endpoint-weighted polynomial approximation with an envelope-bounded taper and payoff of at most logarithmic growth. The error is an integrable BV weight globally, plus a far-negative-jump tail confined to t<b.
-- source:
--   Triangle inequality applied to weighted Bernstein and quantitative taper.

import Mathlib
set_option autoImplicit false
open Set

theorem AvramDividend.Classical.avram_wave5_04c_global_poly_error_from_cutoff_bounds
    (g : ℝ → ℝ) (G : C(unitInterval.Elem, ℝ)) (Q : Polynomial ℝ)
    (b ε K : ℝ)
    (hQ : ∀ t : unitInterval.Elem,
      |Polynomial.eval (t : ℝ) Q - (1 - (t : ℝ)) * G t| ≤
        ε * (1 - (t : ℝ)))
    (hmatch : ∀ t : unitInterval.Elem, b ≤ (t : ℝ) →
      (1 - (t : ℝ)) * G t = g (t : ℝ))
    (hG : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |(1 - (t : ℝ)) * G t| ≤ K * |Real.log (t : ℝ)|)
    (hg : ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |g (t : ℝ)| ≤ K * |Real.log (t : ℝ)|) :
    ∀ t : unitInterval.Elem, 0 < (t : ℝ) →
      |Polynomial.eval (t : ℝ) Q - g (t : ℝ)| ≤
        ε * (1 - (t : ℝ)) +
          (if (t : ℝ) < b then 2 * K * |Real.log (t : ℝ)| else 0) := by sorry
