-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_intervalKernel_isSFinite_of_eq
-- name    : AvramDividend.Classical.runningSup_intervalKernel_isSFinite_of_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:45:18.681719+00:00
-- url     : https://prove2.me/theorems/55548f42-22ee-4f98-a484-e31c9a2dc4ed
-- title:
--   Actual interval-restricted dividend Stieltjes random-measure kernel is s-finite
-- statement:
--   Any kernel that agrees samplewise with the true spectrally negative Lévy running-supremum dividend Stieltjes measure restricted to a fixed half-open real-time interval is s-finite. The pointwise mass is finite by the accepted exact running-record dividend increment formula. Apply the generic constructive theorem that a measurable kernel with finite total mass on every sample path is s-finite. The matching kernel is an explicit argument to avoid canonical parser failures from helper theorem expressions embedded in the target's instance binder.
-- source:
--   Dependency-gated kernel_isSFinite_of_pointwise_finite (staged generic constructive s-finiteness proof) and remotely ACCEPTED runningSup_dividendMeasure_Ioc_lt_top target fbd92a8a-a9ce-4153-83c7-45867f6a929b, candidate 12147.

import Theorems.Thm_AvramDividend_Classical_kernel_isSFinite_of_pointwise_finite
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_lt_top

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_intervalKernel_isSFinite_of_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (l u : ℝ)
    (κ : ProbabilityTheory.Kernel Ω ℝ)
    (hκ : ∀ ω : Ω,
      κ ω = (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) :
    ProbabilityTheory.IsSFiniteKernel κ := by sorry
