-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18p1b_fatou_large_negative_tail
-- name    : AvramDividend.Classical.avram_ja18p1b_fatou_large_negative_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:34:33.582731+00:00
-- url     : https://prove2.me/theorems/363ad99d-91be-4e9b-bccf-ca97a83952d5
-- title:
--   Finite negative first moment from uniform exponential-difference integral bound
-- statement:
--   Generic Fatou theorem for any real measure: uniformly bounded negative-tail integrals of (1-exp(theta*z))/theta for theta down to zero force finite absolute first moment over z≤-1. Does not require a random process.
-- source:
--   J-A18 necessary Fatou analytic child of Open 222788b6.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18p1b_fatou_large_negative_tail
    (ν : Measure ℝ) (D : ℝ)
    (hBound : ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
      (∫⁻ z in Iic (-1 : ℝ),
        ENNReal.ofReal ((1 - Real.exp (θ * z)) / θ) ∂ν) ≤
        ENNReal.ofReal D) :
    (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂ν) < ⊤ := by sorry
