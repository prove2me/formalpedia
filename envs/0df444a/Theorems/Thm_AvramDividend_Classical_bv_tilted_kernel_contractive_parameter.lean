-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_tilted_kernel_contractive_parameter
-- name    : AvramDividend.Classical.bv_tilted_kernel_contractive_parameter
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-05T21:49:40.395679+00:00
-- url     : https://prove2.me/theorems/48970572-99a7-4cf4-9073-6c22345ebbcc
-- title:
--   A contractive Laplace parameter for the canonical BV tilted renewal kernel
-- statement:
--   For a canonical Standing bounded-variation spectrally negative Lévy process and q>0, some integer-derived discount t=n+1 yields a positive shifted parameter s=t-q/X.drift at which the positive tilted-kernel Laplace mass is strictly smaller than X.drift. This is the exact process-level contractivity input for the geometric renewal construction.
-- source:
--   Composition of the already-Proved bv_renewal_kernel_contractivity_of_standing with the generic positive_tilted_kernel_contractivity_of_discount_bound. Positive drift is derived directly from Standing and BoundedVariation as in the accepted contractivity proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_tilted_kernel_contractive_parameter {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) :
    ∃ n : ℕ,
      let t : ℝ := (n : ℝ) + 1
      let a : ℝ := q / X.drift
      let s : ℝ := t - a
      0 < s ∧
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal
            ((1 - Real.exp (-(s + a) * (z : ℝ))) / s)
            ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) <
          ENNReal.ofReal X.drift := by
  sorry
