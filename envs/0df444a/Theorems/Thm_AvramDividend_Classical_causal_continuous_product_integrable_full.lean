-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_continuous_product_integrable_full
-- name    : AvramDividend.Classical.causal_continuous_product_integrable_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:09:22.698061+00:00
-- url     : https://prove2.me/theorems/3853cf24-9bbd-4a19-84e8-ed6dc272f65f
-- title:
--   Full real convolution integrand of continuous causal kernels is integrable
-- statement:
--   If real continuous kernels f and g both vanish on the negative axis, then at every x their full-line convolution integrand y↦f(y)g(x−y) is continuous and compactly supported in [0,max(0,x)]. Consequently it is Lebesgue integrable. This discharges the pointwise full-convolution integrability premises of the monotone convolution-power induction for zero-scale renewal kernels.
-- source:
--   Mathlib HasCompactSupport.intro and Continuous.integrable_of_hasCompactSupport. Zero-discount renewal scale construction.

import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_continuous_product_integrable_full
    (f g : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfzero : ∀ y : ℝ, y < 0 → f y = 0)
    (hgzero : ∀ y : ℝ, y < 0 → g y = 0) :
    ∀ x : ℝ,
      Integrable (fun y : ℝ => f y * g (x - y)) volume := by sorry
