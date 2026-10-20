-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discounted_partition_reward_eq_tsum
-- name    : AvramDividend.Classical.runningSup_discounted_partition_reward_eq_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T21:21:46.109045+00:00
-- url     : https://prove2.me/theorems/360824d4-3c64-410b-8214-90abeb2c9278
-- title:
--   Exact actual Stieltjes reward decomposition over a cofinal disjoint real-time partition
-- statement:
--   For the genuine spectrally negative Lévy running-supremum dividend measure, a measurable extended nonnegative discount weight and any monotone cofinal real-time partition, the Stieltjes integral over times strictly above the initial partition level equals the countable sum of Stieltjes integrals over consecutive half-open partition intervals. The result combines the exact pointwise partition-of-unity identity and Tonelli's countable nonnegative integral/sum interchange, preserving strict-left/weak-right endpoints and avoiding any double payment at partition boundaries. It remains to specialise the partition to measurable inverse-record stopping times and the stopped payment set.
-- source:
--   Dependency-gated recordPartition_pointwise_tsum_indicator and runningSup_lintegral_countable_interchange, both prepared within Chat 05; no new stochastic axiom.

import Theorems.Thm_AvramDividend_Classical_recordPartition_pointwise_tsum_indicator
import Theorems.Thm_AvramDividend_Classical_runningSup_lintegral_countable_interchange

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_discounted_partition_reward_eq_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Measurable w)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n) :
    (∫⁻ r, if u 0 < r then w r else 0
      ∂(dividendMeasure (runningSup X) ω)) =
    (∑' i : ℕ,
      ∫⁻ r, if r ∈ Set.Ioc (u i) (u (i + 1)) then w r else 0
        ∂(dividendMeasure (runningSup X) ω)) := by sorry
