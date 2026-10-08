-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_tilt_product_deriv
-- name    : AvramDividend.Classical.esscher_tilt_product_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:23:35.095534+00:00
-- url     : https://prove2.me/theorems/adac83cf-d6e6-4dcb-bec4-9b965dec1298
-- title:
--   Derivative of an exponential Esscher tilt times a differentiable scale-factor function
-- statement:
--   The derivative of an exponential tilt e^(θx)G(x) at a is e^(θa)[θG(a)+G'(a)] whenever G is differentiable at a. This elementary identity is the analytic core of deriving strict positivity of W^(q)'(a) from the Esscher-scale representation W^(q)(x)=e^(Φ(q)x)W_Φ(x). It uses ordinary product and chain differentiation and does not assume the desired barrier value identity.
-- source:
--   Exponential Esscher scale-function factorisation for spectrally negative Lévy processes: MDPI Risks 2019 7(4)121 equation (25), and Mathlib product and exponential derivative rules.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_tilt_product_deriv
    (θ a : ℝ) (G : ℝ → ℝ)
    (hG : DifferentiableAt ℝ G a) :
    deriv (fun x : ℝ => Real.exp (θ * x) * G x) a =
      Real.exp (θ * a) * (θ * G a + deriv G a) := by sorry
