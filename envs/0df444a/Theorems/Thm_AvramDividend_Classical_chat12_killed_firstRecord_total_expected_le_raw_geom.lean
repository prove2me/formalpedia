-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_total_expected_le_raw_geom
-- name    : AvramDividend.Classical.chat12_killed_firstRecord_total_expected_le_raw_geom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T17:25:37.78661+00:00
-- url     : https://prove2.me/theorems/34d16b4b-f703-498c-aeec-d2c8c52fbce8
-- title:
--   Total killed-record expected reward bounded by raw exit geometric renewal series
-- statement:
--   Summing the fully Proved raw upper geometric killed-record expected reward bound across all levels yields a global upper estimate on total expected killed-record payments: the sum over record-index expectations is bounded by a geometric series in the true discounted strict two-sided-exit expectation multiplied by the zero-th record expected reward. This is an order-theoretic consequence of ENNReal.tsum_le_tsum, independent of the still-Open q-scale exit identity and any dividend-measure pathwise budget.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Theorems.Thm_AvramDividend_Classical_chat12_killed_firstRecord_raw_upper_geometric

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_killed_firstRecord_total_expected_le_raw_geom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) :
    (∑' n : ℕ, (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
        else 0 ∂P)) ≤
      (∑' n : ℕ, (∫⁻ ω, if
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
        (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
          ENNReal.ofReal (Real.exp
            (-(q * ENNReal.toReal
              (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
        else 0 ∂P) ^ n * (∫⁻ ω, if twoSidedExitUpTime X ((0 : ℝ) * ε) ω <
            barrierRuinTime X a ω then
          ENNReal.ofReal (ε * Real.exp
            (-(q * (twoSidedExitUpTime X ((0 : ℝ) * ε) ω).toReal)))
        else 0 ∂P)) := by sorry
