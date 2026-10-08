-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_quadratic_laplace
-- name    : AvramDividend.Classical.scaleFunction_strict_pos_of_quadratic_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T09:49:15.843736+00:00
-- url     : https://prove2.me/theorems/40da2a27-bad0-4f77-9241-e5330fe8a860
-- title:
--   Strict positivity of a monotone scale function from its quadratic-bounded Laplace exponent
-- statement:
--   For any nonnegative nondecreasing W on [0,∞), if for all β≥β0 its positive Laplace transform equals 1/(ψ(β)-q) and ψ(β)-q is at most quadratic, then W is strictly positive on (0,∞). The conclusion is purely analytic and does not assume an Esscher transform or stochastic exit identity.
-- source:
--   Compose the separately authored Laplace tail estimate, monotone-zero restriction equality, and exponential-versus-quadratic contradiction; bridge to universal Avram scale-function positivity. Publication preamble intentionally excludes as-yet Open auxiliary theorems; the submitted proof may import them as dependency children.

import Mathlib
open MeasureTheory Set Filter

namespace AvramDividend.Classical

theorem scaleFunction_strict_pos_of_quadratic_laplace
    (W ψ : ℝ → ℝ) (q β0 C : ℝ)
    (hW : ∀ x : ℝ, 0 ≤ x → 0 ≤ W x)
    (hmono : MonotoneOn W (Ici 0))
    (hLap : ∀ β : ℝ, β0 ≤ β →
      0 < ψ β - q ∧
      IntegrableOn (fun x : ℝ => Real.exp (-β * x) * W x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), Real.exp (-β * x) * W x) =
        (ψ β - q)⁻¹)
    (hquadratic : ∀ β : ℝ, β0 ≤ β →
      ψ β - q ≤ C * (1 + β ^ 2)) :
    ∀ a : ℝ, 0 < a → 0 < W a := by
  sorry

end AvramDividend.Classical
