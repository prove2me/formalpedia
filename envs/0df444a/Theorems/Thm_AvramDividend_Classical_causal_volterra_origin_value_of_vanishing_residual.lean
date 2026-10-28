-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_volterra_origin_value_of_vanishing_residual
-- name    : AvramDividend.Classical.causal_volterra_origin_value_of_vanishing_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:45:37.722988+00:00
-- url     : https://prove2.me/theorems/f1ea15ab-c6db-4c8c-99fc-99c24286428c
-- title:
--   Zero-time value of a continuous Volterra resolvent from vanishing convolution
-- statement:
--   A continuous derivative resolvent from Gaussian Esscher Volterra theory has the normalisation g(0)=1/a when the residual causal convolution vanishes at zero; take the right limit in a*g(x)+C(x)=1. This is needed for the one-sided Gaussian scale derivative, after identifying the native coefficient a=sigma squared divided by two.
-- source:
--   Volterra second-kind integral equation boundary normalisation by continuity.

import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Algebra.Field.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

namespace AvramDividend.Classical
/-- A continuous second-kind Volterra resolvent has the correct zero-time normalisation. -/
theorem causal_volterra_origin_value_of_vanishing_residual
    (a : ℝ) (g C : ℝ → ℝ) (ha : 0 < a)
    (hg : ContinuousOn g (Ici (0 : ℝ)))
    (hC : Tendsto C (𝓝[>] (0 : ℝ)) (𝓝 0))
    (heq : ∀ x : ℝ, 0 < x → a * g x + C x = 1) :
    g 0 = 1 / a := by
  sorry
end AvramDividend.Classical
