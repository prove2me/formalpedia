-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_exponential_kernel_weight_small
-- name    : AvramDividend.Classical.causal_volterra_exponential_kernel_weight_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T17:13:22.106458+00:00
-- url     : https://prove2.me/theorems/4d81fa95-d3a7-45d8-be31-0ff9f7fdcc9c
-- title:
--   An L1 causal kernel admits an exponentially weighted contraction constant
-- statement:
--   Given a>0, β∈R, and K integrable on the positive half-line, choose a sufficiently large exponential weight λ>0 so that |β|/λ + integral_0^∞ |K(t)|exp(-λt)dt < a. As λ tends to infinity, |β|/λ tends to zero. The exponential factor tends pointwise to zero for each t>0 and is bounded by one for λ≥0, so dominated convergence against |K| shows the weighted K norm tends to zero. This quantitative estimate is the exact contraction threshold for the weighted causal Volterra operator.
-- source:
--   Lebesgue dominated convergence theorem and exponential Laplace damping of an integrable kernel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.causal_volterra_exponential_kernel_weight_small
    (K : ℝ → ℝ) (a β : ℝ)
    (ha : 0 < a)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume) :
    ∃ weight : ℝ, 0 < weight ∧
      |β| / weight +
        (∫ t in Ioi (0 : ℝ),
          |K t| * Real.exp (-weight * t) ∂volume) < a := by sorry
