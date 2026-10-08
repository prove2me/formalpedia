-- Prove2me | Theorems.Thm_AvramDividend_Classical_interval_exponential_of_positive_log_derivative
-- name    : AvramDividend.Classical.interval_exponential_of_positive_log_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:13:03.278809+00:00
-- url     : https://prove2.me/theorems/3bb793af-d04c-4040-a2bc-a16900996da2
-- title:
--   Integrated exponential formula from a continuous logarithmic derivative
-- statement:
--   For a function V>0 on positive reals with derivative V'=V*g and with continuous g on positive reals, the fundamental theorem of calculus applied to log V yields log V(b)-log V(a)=∫_a^b g. Exponentiation produces V(b)=V(a)*exp(∫ g). This avoids stochastic excursion theory and is a generic analytic ingredient for the shape/log-derivative approach.
-- source:
--   Pinned Mathlib HasDerivAt.log and intervalIntegral.integral_eq_sub_of_hasDerivAt.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology ENNReal

theorem AvramDividend.Classical.interval_exponential_of_positive_log_derivative
    (V g : ℝ → ℝ)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hgcont : ContinuousOn g (Ioi (0 : ℝ)))
    (hVderiv : ∀ x : ℝ, 0 < x → HasDerivAt V (V x * g x) x) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      V b = V a * Real.exp (∫ t in a..b, g t) := by sorry
