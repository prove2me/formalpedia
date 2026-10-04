-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_jump_compensator_lintegral_tendsto_zero
-- name    : AvramDividend.Classical.discounted_jump_compensator_lintegral_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-03T21:53:47.82299+00:00
-- url     : https://prove2.me/theorems/fd006cea-d2f7-4f75-b99e-6f3b67cc3a88
-- title:
--   Discounted Lévy compensator integral decays by dominated convergence
-- statement:
--   Let μ be a measure of nonnegative jump magnitudes with finite truncated first moment ∫min(z,1)μ(dz). Along θ=n+1 the nonnegative integral of (1-exp(-θz))/θ tends to zero. This follows from the uniform bound by min(z,1) and Mathlib's nonnegative dominated convergence theorem. It is the key analytic step proving that the exponentially discounted bounded-variation Lévy renewal kernel eventually has total mass less than the positive drift.
-- source:
--   Pinned Mathlib MeasureTheory.Integral.Lebesgue.DominatedConvergence theorem tendsto_lintegral_of_dominated_convergence; Avram dividend BV renewal kernel

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

/-- Integer-parameter decay of the discounted positive Lévy jump compensator
under the bounded-variation truncated-first-moment hypothesis. -/
theorem discounted_jump_compensator_lintegral_tendsto_zero (μ : Measure ℝ≥0)
    (hμ : (∫⁻ z : ℝ≥0,
       ENNReal.ofReal (min (z : ℝ) 1) ∂μ) ≠ ⊤) :
    Tendsto (fun n : ℕ =>
      ∫⁻ z : ℝ≥0,
        ENNReal.ofReal
          ((1 - Real.exp (-((n : ℝ) + 1) * (z : ℝ))) /
            ((n : ℝ) + 1)) ∂μ)
      Filter.atTop (𝓝 (0 : ℝ≥0∞)) := by
  sorry

end AvramDividend.Classical
