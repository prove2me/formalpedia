-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_fixed_renewal_cumulative_positiveLaplace
-- name    : AvramDividend.Classical.bv_fixed_renewal_cumulative_positiveLaplace
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:16:03.963981+00:00
-- url     : https://prove2.me/theorems/d4968d30-3884-4761-bd03-1d98c7ddc30c
-- title:
--   One bounded-variation renewal measure has the shifted cumulative positive Laplace formula on a whole half-line
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process and q>0, construct one positive geometric renewal measure β and the Esscher tilt φ=q/drift. β has finite lower cumulative mass everywhere and a positive atom at zero. There is one positive anchor b such that for every s≥b, the nonnegative Laplace transform of x↦β((−∞,x]) equals the explicit geometric renewal expression formed from the shifted positive jump-magnitude transform at s+φ. Crucially, β is fixed before s varies. This is the measure-theoretic half-line family immediately preceding identification with the q-scale function.
-- source:
--   Proved bv_supported_positive_kernel_transform_gap UUID 53172041-5bc2-4a46-99fe-0132e91bced4; Proved positive_geometric_renewal_measure_package, positiveLaplace_convolution_powers, positiveLaplace_geometric_measure_sum, positiveLaplace_cumulative_measure; pinned Mathlib support and ENNReal arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_fixed_renewal_cumulative_positiveLaplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      0 < β {0} ∧
      ∀ s : ℝ, b ≤ s →
        (∫⁻ x : ℝ in Ioi 0,
          ENNReal.ofReal (Real.exp (-s * x)) * β (Iic x)) =
        ENNReal.ofReal (1 / s) *
          ((ENNReal.ofReal X.drift)⁻¹ *
            (1 - (ENNReal.ofReal X.drift)⁻¹ *
              (∫⁻ z : ℝ≥0, ENNReal.ofReal
                ((1 - Real.exp (-(s + φ) * (z : ℝ))) / s)
                ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))))⁻¹) := by sorry
