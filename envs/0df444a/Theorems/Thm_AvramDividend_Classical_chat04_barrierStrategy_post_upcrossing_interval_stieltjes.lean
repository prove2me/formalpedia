-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_post_upcrossing_interval_stieltjes
-- name    : AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_interval_stieltjes
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:36:10.608967+00:00
-- url     : https://prove2.me/theorems/ca83cccd-c8dc-470a-8233-ab72fdb8502f
-- title:
--   Equal barrier and record Stieltjes mass on every interval after first crossing
-- statement:
--   On every interval (r,s] entirely after the finite first strict upcrossing u, the barrier dividend strategy and original running supremum have identical Lebesgue–Stieltjes mass, under boundedness of the Lévy path through s. The proof combines the exact interval-increment corollary with monotonicity and right-continuity of both strategies, thus extending the previously proved anchored (u,u+t] equality to a generating family of all post-crossing intervals.
-- source:
--   Theorem derived from forthcoming interval increment bridge and Proved generic Stieltjes transfer, both in this mission.

import Theorems.Thm_AvramDividend_Classical_chat04_barrierStrategy_post_upcrossing_interval_increment
import Theorems.Thm_AvramDividend_Classical_chat04_stieltjes_Ioc_eq_of_right_continuous_increment
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous_below_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_continuous
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_barrierStrategy_post_upcrossing_interval_stieltjes
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hx0 : 0 ≤ x) (ha0 : 0 ≤ a) (hxa : x ≤ a)
    (ω : Ω) (u r s : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (v : ℝ≥0) (_ : a - x < X.X v ω), (v : ℝ≥0∞)))
    (hur : u ≤ r) (hrs : r ≤ s)
    (hb : BddAbove ((fun v : ℝ≥0 => X.X v ω) '' Set.Icc 0 s)) :
    (dividendMeasure (barrierStrategy X x a) ω)
      (Set.Ioc (r : ℝ) (s : ℝ)) =
    (dividendMeasure (runningSup X) ω)
      (Set.Ioc (r : ℝ) (s : ℝ)) := by sorry
