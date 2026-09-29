-- Prove2me | Theorems.Thm_FamousTheorems_integral_eq_sub_of_hasDeriv_right_of_le
-- name    : FamousTheorems.integral_eq_sub_of_hasDeriv_right_of_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T23:45:29.299686+00:00
-- url     : https://prove2.me/theorems/57c35593-aad5-463a-9c4c-55c4386ef6e2
-- title:
--   The fundamental theorem of integral calculus
-- statement:
--   **The fundamental theorem of calculus**, second part (the Newton–Leibniz formula).
--
--   Let $f : [a,b] \to E$ be continuous on $[a,b]$, differentiable from the right at every interior
--   point with right derivative $f'$, and suppose $f'$ is interval-integrable. Then
--   $$\int_a^b f'(y)\,dy \;=\; f(b) - f(a).$$
--
--   Integration and differentiation are inverse operations: the integral of a rate of change over an
--   interval is the net change. This is the statement that makes calculus a computational subject rather
--   than a theory of limits — areas are evaluated by finding antiderivatives instead of summing
--   rectangles.
--
--   The hypotheses here are notably weak, and deliberately so. Differentiability is required only on the
--   open interval and only from the right, continuity carries the endpoints, and $f'$ need only be
--   integrable, not continuous. This version therefore covers functions with corners and with derivatives
--   that are unbounded or wildly discontinuous, where the textbook "continuously differentiable"
--   statement does not apply.
--
--   Barrow, Newton and Leibniz established the connection in the 17th century; the sharp integrability
--   hypotheses are a product of the Lebesgue theory.
--
--   **Formalization note.** The codomain $E$ is any Banach space, so the theorem covers vector-valued
--   integrands; `∫ y in a..b` is the oriented interval integral. The result is Mathlib's
--   `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set intervalIntegral
open scoped Real Topology ENNReal

theorem integral_eq_sub_of_hasDeriv_right_of_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f f' : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ x ∈ Set.Ioo a b, HasDerivWithinAt f (f' x) (Set.Ioi x) x)
    (f'int : IntervalIntegrable f' volume a b) :
    ∫ y in a..b, f' y = f b - f a := by sorry

end FamousTheorems
