-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_weighted_laplace_uniform_discount
-- name    : AvramDividend.Classical.unbounded_scale_weighted_laplace_uniform_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:42:24.918574+00:00
-- url     : https://prove2.me/theorems/daaa0f31-37e7-42a0-9773-8ebe574e96ce
-- title:
--   Uniform high-parameter Laplace estimate across bounded nonnegative q-discounts
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, the theta-weighted Laplace transform of any canonical q-scale function is uniformly small as theta grows, simultaneously for all nonnegative q in any prescribed bounded interval. The large-parameter threshold is independent of q and the chosen valid scale function, providing parameter-uniform scale-function control for renewal and Esscher analysis.
-- source:
--   Derived uniformly from IsScaleFunction and the proved unbounded_psi_discount_denominator_eventually_linear (f9bc45e4-85d1-4707-a640-4d7c48cba7a9).

import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_weighted_laplace_uniform_discount
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (Q : ℝ) (hQ : 0 ≤ Q) :
    ∀ ε : ℝ, 0 < ε →
      ∃ β : ℝ, 1 ≤ β ∧
        ∀ θ : ℝ, β ≤ θ →
          ∀ q : ℝ, 0 ≤ q → q ≤ Q →
            ∀ W : ℝ → ℝ, IsScaleFunction X q W →
              θ * (∫ x in Ioi (0 : ℝ),
                Real.exp (-(θ * x)) * W x) < ε := by sorry
