-- Prove2me | Theorems.Thm_DiazModulus_real_axis_exp_unit_circle
-- name    : DiazModulus.real_axis_exp_unit_circle
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-10-04T03:30:53.983973+00:00
-- url     : https://prove2.me/theorems/a924ac77-9848-41c9-b3dd-f2fd89933cdf
-- title:
--   Real-axis exponential lies on the unit circle
-- statement:
--   On the real axis the exponential value lies on the unit circle: if
--   `γ.im = 0` then `‖e^{γ/(iπ)}‖ = 1`.

import Mathlib

namespace DiazModulus
theorem real_axis_exp_unit_circle :
    ∀ γ : ℂ, γ.im = 0 →
      ‖Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))‖ = 1 := by sorry
end DiazModulus
