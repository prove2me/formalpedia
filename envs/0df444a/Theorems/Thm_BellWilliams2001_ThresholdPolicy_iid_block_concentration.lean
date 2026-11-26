-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_iid_block_concentration
-- name    : BellWilliams2001.ThresholdPolicy.iid_block_concentration
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T05:54:07.346158+00:00
-- url     : https://prove2.me/theorems/90413267-e2d7-59de-ad14-359d356627d0
-- title:
--   Two-sided exponential concentration for blocks of i.i.d. centered increments
-- statement:
--   Let the increments be independent and identically distributed, centered, and have exponential moments in a neighborhood of zero. For each positive tolerance, the probability that the absolute sum of a block exceeds the tolerance times the block length is at most twice a geometric term in that length. The bound is uniform over the starting index of the block.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Cramér estimates in Appendix A and their use in Section 7

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

theorem iid_block_concentration {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hm : ∀ j, Measurable (X j))
    (hi : iIndepFun X P) (hId : ∀ j, IdentDistrib (X j) (X 0) P P)
    (hMean : ∫ ω, X 0 ω ∂P = 0)
    (hmom : ∃ a > 0, ∀ u ∈ Ioo (-a) a, Integrable (fun ω => Real.exp (u * X 0 ω)) P)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ j m : ℕ,
      P {ω | δ * m ≤ |∑ i ∈ Finset.range m, X (j+i) ω|} ≤ ENNReal.ofReal (2 * ρ^m) := by sorry

end BellWilliams2001.ThresholdPolicy
