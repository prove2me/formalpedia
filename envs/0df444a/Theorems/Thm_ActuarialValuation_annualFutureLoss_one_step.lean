-- Prove2me | Theorems.Thm_ActuarialValuation_annualFutureLoss_one_step
-- name    : ActuarialValuation.annualFutureLoss_one_step
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:21:46.289677+00:00
-- url     : https://prove2.me/theorems/947a7fdc-5e00-49d3-9435-5d2c30ad8cca
-- title:
--   Pointwise annual loss recursion
-- statement:
--   The current-year premium and reserve balance the death claim and discounted surviving continuation in each lifetime outcome.
--
--   **Mathematical statement**
--
--   $$
--   L_t+\pi\mathbf1_{\{K\ge t\}}=vb\mathbf1_{\{K=t\}}+vL_{t+1}
--   $$
-- source:
--   Gerber, Life Insurance Mathematics (1997, third edition), Ch.6 §6.3, equations (6.3.4)-(6.3.10); Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks (2009), Ch.7 §7.3.3, https://doi.org/10.1017/CBO9780511800146.008

import Mathlib
import Definitions.Def_actuarial_annualFutureLoss
open MeasureTheory

namespace ActuarialValuation

theorem annualFutureLoss_one_step {Ω : Type*} (K : Ω → ℕ) (v : ℝ) (n t : ℕ) (b π : ℝ) (ω : Ω) (ht : t < n)
  :
  annualFutureLoss K v n t b π ω + (if t ≤ K ω then π else 0) =
    (if K ω = t then v * b else 0) +
      v * annualFutureLoss K v n (t + 1) b π ω := by sorry

end ActuarialValuation
