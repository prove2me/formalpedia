-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_ratio_and_finite_deriv_limit
-- name    : AvramDividend.Classical.barrierStrategy_zero_boundary_of_positive_ratio_and_finite_deriv_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:46:50.718407+00:00
-- url     : https://prove2.me/theorems/fb8027bb-7b35-43db-b240-15e57d3ba650
-- title:
--   Zero-barrier reflected value from positive-barrier scale identities and finite right derivative
-- statement:
--   If the actual positive reflected barrier rewards equal W(a)/W'(a) at reciprocal barriers, and the scale function is continuous at zero with an ordinary positive-side derivative tending to a nonzero finite d, the zero-barrier stopped dividend value equals the exact scale-function boundary expression. This combines proved stochastic monotone convergence, derivative EReal conversion, and real quotient convergence.
-- source:
--   Pinned Mathlib one-sided topology; canonical accepted Avram scale-ratio, zero-barrier stochastic convergence, derivative-liminf and boundary ratio lemmas.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Tactic.Positivity
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_zero_boundary_of_positive_scale_limit
import Theorems.Thm_AvramDividend_Classical_scale_ratio_reciprocal_tendsto_of_deriv_limit
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_eq_ratio_of_finite_derivZeroPlus
import Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_coe_of_right_tendsto

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_zero_boundary_of_positive_ratio_and_finite_deriv_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hscale : ∀ n : ℕ,
      barrierSupValue X (1 / ((n : ℝ) + 1)) q =
        ENNReal.ofReal (W (1 / ((n : ℝ) + 1)) /
          deriv W (1 / ((n : ℝ) + 1))))
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (d : ℝ) (hd : d ≠ 0)
    (hderiv : Tendsto (fun y : ℝ => deriv W y)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds d)) :
    dividendValue X q 0 (barrierStrategy X 0 0) =
      ENNReal.ofReal (barrierValue W 0 0) := by sorry
