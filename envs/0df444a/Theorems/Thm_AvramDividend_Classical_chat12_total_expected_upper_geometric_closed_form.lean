-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_geometric_closed_form
-- name    : AvramDividend.Classical.chat12_total_expected_upper_geometric_closed_form
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:44:42.388602+00:00
-- url     : https://prove2.me/theorems/f21990f0-0369-4cdc-b1d7-54fa24838478
-- title:
--   Closed-form total discounted expected killed records from strict-exit factor
-- statement:
--   If the true discounted strict two-sided-exit expectation equals ENNReal.ofReal p with p≥0, then the total expected discounted payments across all killed upward-record levels is at most ENNReal.ofReal epsilon multiplied by (1 - ENNReal.ofReal p)^(-1). It combines the Proved geometric upper record budget summed termwise with the unshifted ENNReal geometric-series identity. The result remains valid in extended nonnegative reals when the geometric series diverges and leaves the scale-function ratio identification as a separate hypothesis.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_chat12_total_expected_upper_le_scalar_geometric_tsum
import Theorems.Thm_AvramDividend_Classical_chat12_ofReal_geometric_tsum_unshifted

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_total_expected_upper_geometric_closed_form
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (p : ℝ) (hp : 0 ≤ p)
    (hExit : (∫⁻ ω, if
          (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal p) :
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P)) ≤
      ENNReal.ofReal ε * (1 - ENNReal.ofReal p)⁻¹ := by sorry
