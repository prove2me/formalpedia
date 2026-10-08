-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_shifted_kernel_gap_on_halfline
-- name    : AvramDividend.Classical.bv_shifted_kernel_gap_on_halfline
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T06:26:57.84268+00:00
-- url     : https://prove2.me/theorems/ea5b1659-9f7a-43e7-8b57-75f34e0c8547
-- title:
--   The BV shifted renewal-kernel transform remains contractive on a whole half-line
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process and q>0, set φ=q/drift. There exists a positive discount anchor b such that for every s≥b, the shifted positive jump-magnitude renewal-kernel transform at s+φ remains strictly smaller than the positive BV drift. The proved supported-kernel theorem gives the strict gap at one b. Because the kernel is supported on nonnegative reserve levels, its positive exponential Laplace transform is nonincreasing in s, so the same strict gap persists for every larger discount. The exact kernel-transform identity then rewrites the result in jump-magnitude form.
-- source:
--   Proved bv_supported_positive_kernel_transform_gap UUID 53172041-5bc2-4a46-99fe-0132e91bced4 and bv_standing_drift_pos; elementary lintegral monotonicity on nonnegative support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_shifted_kernel_gap_on_halfline
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hbv : X.BoundedVariation) :
    ∃ (φ b : ℝ), 0 < φ ∧ 0 < b ∧
      ∀ s : ℝ, b ≤ s →
        (∫⁻ z : ℝ≥0, ENNReal.ofReal
          ((1 - Real.exp (-(s + φ) * (z : ℝ))) / s)
          ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y)))) <
          ENNReal.ofReal X.drift := by sorry
