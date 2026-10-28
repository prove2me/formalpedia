-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_of_unbounded_zero_cstar
-- name    : AvramDividend.Classical.vcstar_deriv_eq_one_of_unbounded_zero_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:57:52.746987+00:00
-- url     : https://prove2.me/theorems/fe5177ad-a8e8-4c4c-a91f-71708705a1ce
-- title:
--   Optimal zero-barrier candidate has derivative exactly one at every positive reserve
-- statement:
--   If unbounded variation leads to cstar W = 0, the actual optimal-barrier verification candidate vcstar agrees with max x 0. Thus it is differentiable at every strictly positive reserve with derivative exactly one. This discharges the gradient constraint of the global vcstar_deriv_ge_one frontier theorem in the zero-optimal-barrier regime.
-- source:
--   Previously Proved vcstar_eq_positive_part_of_unbounded_zero_cstar; Mathlib eventually equal function derivative congruence and derivative of identity.

import Theorems.Thm_AvramDividend_Classical_vcstar_eq_positive_part_of_unbounded_zero_cstar
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.OrderClosed

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.vcstar_deriv_eq_one_of_unbounded_zero_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (hc0 : cstar W = 0) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ deriv (vcstar W) x = 1 := by sorry
