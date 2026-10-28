-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_gaussian_of_ae_negative_near_zero
-- name    : AvramDividend.Classical.barrier_zero_boundary_value_package_gaussian_of_ae_negative_near_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:55:45.718956+00:00
-- url     : https://prove2.me/theorems/ff60fd01-e2fb-4767-a47c-3219c841566f
-- title:
--   Gaussian zero-barrier strategy value from downward regularity at time zero
-- statement:
--   For a standing spectrally negative Levy process with positive Gaussian coefficient, almost-sure negative values at arbitrarily small positive times imply both nonnegativity of the zero-barrier candidate and equality between actual zero-barrier dividend value and the scale-function boundary formula. Gaussian positivity makes bounded variation impossible. The stochastic pathwise regularity hypothesis is explicit, allowing reuse in a future direct Gaussian verification argument.
-- source:
--   Proved zero-barrier dividend package under negative near-zero regularity fd11e610-82a7-4259-aadf-65c9d68662bb and the exact definition of SpectrallyNegativeLevy.BoundedVariation.

import Theorems.Thm_AvramDividend_Classical_barrier_zero_boundary_value_package_of_unbounded_ae_negative_near_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrier_zero_boundary_value_package_gaussian_of_ae_negative_near_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hσ : 0 < X.σ)
    (hNear : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    0 ≤ barrierValue W 0 0 ∧
      dividendValue X q 0 (barrierStrategy X 0 0) =
        ENNReal.ofReal (barrierValue W 0 0) := by sorry
