-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tail_integral_shift_identity
-- name    : AvramDividend.Classical.esscher_tail_integral_shift_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T22:39:49.596833+00:00
-- url     : https://prove2.me/theorems/3ed689c3-5602-44e5-8acc-c26695b97cac
-- title:
--   Exact Esscher-shifted negative-jump tail kernel cancellation
-- statement:
--   For any real-valued jump-tail density κ, whenever both original weighted-tail kernels are Lebesgue integrable on (0,∞), the difference of the original Laplace kernels at Φ+s and Φ integrates to the Esscher-weighted jump-tail kernel exp(-Φt)(1-exp(-st))κ(t). The identity is real-integral subtraction of two FINITE quantities and uses exact exponential addition; it is the deterministic step needed to transform ψ(Φ+s)/(Φ+s) into a Bernstein exponent after subtracting the original baseline ψ(Φ)/Φ. No assumption of finite ∫κ is made.
-- source:
--   Original Lévy exponent to negative-tail representation 0fded7ba and ladder renewal source 2fa29eaf; Mathlib Real.exp_add and MeasureTheory.integral_sub.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.esscher_tail_integral_shift_identity
    (κ : ℝ → ℝ) (Φ s : ℝ)
    (hNext : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-((Φ + s) * t))) * κ t) (Ioi (0 : ℝ)))
    (hBase : IntegrableOn
      (fun t : ℝ => (1 - Real.exp (-(Φ * t))) * κ t) (Ioi (0 : ℝ))) :
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-((Φ + s) * t))) * κ t) -
    (∫ t in Ioi (0 : ℝ),
      (1 - Real.exp (-(Φ * t))) * κ t) =
    (∫ t in Ioi (0 : ℝ),
      Real.exp (-(Φ * t)) * (1 - Real.exp (-(s * t))) * κ t) := by sorry
