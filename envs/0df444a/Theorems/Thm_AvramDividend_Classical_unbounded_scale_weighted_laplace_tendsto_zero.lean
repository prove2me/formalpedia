-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_scale_weighted_laplace_tendsto_zero
-- name    : AvramDividend.Classical.unbounded_scale_weighted_laplace_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:29:44.963992+00:00
-- url     : https://prove2.me/theorems/15ad5b76-dcc6-4dd3-81dd-f4c23d80a7a4
-- title:
--   Vanishing large-parameter normalised Laplace transform of an unbounded-variation q-scale function
-- statement:
--   For an unbounded-variation spectrally negative Lévy process with nonnegative discount, any canonical q-scale function has θ times its positively supported Laplace transform converging to zero as θ tends to infinity. The result converts exponent growth into a direct weighted-integral asymptotic for the scale function.
-- source:
--   Definition IsScaleFunction and the proved unbounded_psi_discount_denominator_eventually_linear (f9bc45e4-85d1-4707-a640-4d7c48cba7a9) and unbounded_psi_discount_reciprocal_tendsto_zero (03e77a7a-cc5e-46f0-ae71-a02beea42c14).

import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_scale_weighted_laplace_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    Tendsto
      (fun θ : ℝ => θ * (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * W x))
      atTop (nhds 0) := by sorry
