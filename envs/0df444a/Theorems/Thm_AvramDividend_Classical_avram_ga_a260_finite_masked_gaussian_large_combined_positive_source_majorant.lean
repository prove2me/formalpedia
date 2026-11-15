-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a260_finite_masked_gaussian_large_combined_positive_source_majorant
-- name    : AvramDividend.Classical.avram_ga_a260_finite_masked_gaussian_large_combined_positive_source_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:50:19.559487+00:00
-- url     : https://prove2.me/theorems/b43c1ea6-a6c3-4752-9184-04ce02d9f020
-- title:
--   Masked original Gaussian finite-grid combined positive large-cell source dominated by nonnegative endpoint/energy sum
-- statement:
--   For any true finite Gaussian mesh and a mask selecting source large increments, each cell’s discounted combined Taylor and Hessian residual obeys the one-sided positive envelope a258 when its initial compact value/jet and endpoint upper bounds are supplied. The positive part of the masked finite sum is bounded by the masked sum of endpoint upper envelopes plus compact initial value, raw modulus and squared centred Gaussian energy. This is the exact source finite-sum aggregation needed to combine large-cell exponential expected L1 a233 with large raw-square expected L1 a187 in the original a216 verification.
-- source:
--   a258 combined large-cell pointwise; finite mesh sum positivity and max bound

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a260_finite_masked_gaussian_large_combined_positive_source_majorant
    {Ω : Type*} (S : Finset ℕ)
    (A : ℕ → Ω → Prop) [∀ i, DecidablePred (A i)]
    (e0 e1 w0 w1 d h r z T : ℕ → Ω → ℝ)
    (B : ℝ) (hB : 0 ≤ B)
    (hCell : ∀ i ω, A i ω →
      0 ≤ e0 i ω ∧ e0 i ω ≤ 1 ∧
      0 ≤ e1 i ω ∧ e1 i ω ≤ 1 ∧
      0 ≤ T i ω ∧ |w0 i ω| ≤ B ∧
      |d i ω| ≤ B ∧ |h i ω| ≤ B ∧
      w1 i ω ≤ T i ω)
    (ω : Ω) :
    max (∑ i ∈ S, if A i ω then
      e1 i ω*(w1 i ω-w0 i ω) -
        e0 i ω*(d i ω*r i ω+h i ω/2*(z i ω)^2)
      else 0) 0 ≤
    ∑ i ∈ S, if A i ω then
      T i ω+B*(1+|r i ω|+(z i ω)^2/2)
      else 0 := by sorry
