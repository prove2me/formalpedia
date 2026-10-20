-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_cumulative_laplace_real_integral_bridge
-- name    : AvramDividend.Classical.positive_cumulative_laplace_real_integral_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T17:23:01.303976+00:00
-- url     : https://prove2.me/theorems/cc36bbe0-53d3-4641-bc9c-c60bd186f30d
-- title:
--   Positive cumulative Laplace equality transfers from ENNReal to integrable real functions
-- statement:
--   Let β have finite lower cumulative masses at every real endpoint. If a nonnegative integrable function fs on the positive half-line has the same positive ENNReal Laplace integral as the exponential weighting of β's lower cumulative, then the weighted real cumulative is integrable and its real integral equals that of fs. This removes a recurring analytic bridge between scale-function Laplace transforms and real dividend valuation formulas.
-- source:
--   Kuznetsov Kyprianou Rivero Theory of Scale Functions transform framework; pinned Prove2Me accepted bv_tilted_cumulative_laplace_representation d7edfe09-24dd-415a-9cae-3e2ba4fc6dba, using Mathlib real/ENNReal integration bridge.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Tactic.FunProp

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_cumulative_laplace_real_integral_bridge
    (β : Measure ℝ) (hβfin : ∀ x : ℝ, β (Iic x) ≠ ⊤)
    (θ : ℝ) (fs : ℝ → ℝ)
    (hfsInt : IntegrableOn fs (Ioi (0 : ℝ)))
    (hfsPos : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fs)
    (hLap :
      (∫⁻ x : ℝ in Ioi 0, ENNReal.ofReal (fs x)) =
      (∫⁻ x : ℝ in Ioi 0,
        ENNReal.ofReal (Real.exp (-θ * x)) * β (Iic x))) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-θ * x) * (β (Iic x)).toReal) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), fs x) =
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-θ * x) * (β (Iic x)).toReal) := by sorry
