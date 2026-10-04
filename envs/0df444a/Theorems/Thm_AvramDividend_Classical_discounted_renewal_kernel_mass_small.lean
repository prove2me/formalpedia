-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_renewal_kernel_mass_small
-- name    : AvramDividend.Classical.discounted_renewal_kernel_mass_small
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T21:56:04.489683+00:00
-- url     : https://prove2.me/theorems/35bb663a-26d9-445a-ac55-600fb4addeb4
-- title:
--   Existence of a contractive discount for the positive BV Lévy renewal kernel
-- statement:
--   For any Lévy jump-magnitude measure with finite truncated first moment, any positive discount q and positive drift δ, some integer θ=n+1 makes q/θ + ∫(1-exp(-θz))/θ μ(dz) strictly smaller than δ. This is the contraction needed to form the positive geometric convolution resolvent for a bounded-variation spectrally negative Lévy q-scale function.
-- source:
--   BV scale-function renewal identity with pinned Mathlib real reciprocal limit and ENNReal dominated convergence

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Some integer discount makes the full BV renewal kernel mass smaller
than an arbitrary positive drift, assuming finite jump truncation mass. -/
theorem discounted_renewal_kernel_mass_small (μ : Measure ℝ≥0)
    (hμ : (∫⁻ z : ℝ≥0, ENNReal.ofReal (min (z : ℝ) 1) ∂μ) ≠ ⊤)
    (q δ : ℝ) (hq : 0 < q) (hδ : 0 < δ) :
    ∃ n : ℕ,
      ENNReal.ofReal (q / ((n : ℝ) + 1)) +
        (∫⁻ z : ℝ≥0,
          ENNReal.ofReal
            ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) /
              ((n : ℝ) + 1)) ∂μ) <
        ENNReal.ofReal δ := by
  sorry

end AvramDividend.Classical
