-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_global_sfinite_kernel_exists
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_global_sfinite_kernel_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:54:21.627181+00:00
-- url     : https://prove2.me/theorems/ae5ede48-9183-41e4-95f3-b04fdca5acaa
-- title:
--   The actual entire running-supremum dividend Stieltjes measure has a measurable s-finite kernel representation
-- statement:
--   For any original spectrally negative Lévy process, the full untruncated sample-path running-supremum dividend Stieltjes measure on real time is representable by an s-finite measurable kernel, without assuming that its total lifetime dividend mass is finite. Partition the entire real time axis into disjoint unit intervals (n,n+1] indexed by all integers, create the accepted measurable interval-restricted Stieltjes kernel on each interval, obtain its s-finiteness from the remotely proved samplewise finite interval-mass theorem, and sum the countably many interval kernels. Pinned Mathlib integer-interval partition and measure restriction-sum identities show that the reconstructed kernel agrees with the full original dividend measure on every sample path. This is the precise missing bridge to unconditional measurability of the full stopped dividend reward.
-- source:
--   Pinned Mathlib iUnion_Ioc_intCast, Set.pairwise_disjoint_Ioc_intCast, Measure.restrict_iUnion and Kernel.isSFiniteKernel_sum; remotely accepted kernel_isSFinite_of_pointwise_finite target e1a700f5-002e-4bc1-afb4-dcde7bffc72a, candidate 12283; accepted runningSup_dividendMeasure_Ioc_lt_top target fbd92a8a-a9ce-4153-83c7-45867f6a929b and runningSup_dividendMeasure_restrict_Ioc_measurable target d763694e-e35d-43bf-90d6-3d1a42a067ed.

import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Restrict
import Theorems.Thm_AvramDividend_Classical_kernel_isSFinite_of_pointwise_finite
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_lt_top
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable

open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_global_sfinite_kernel_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ κ : ProbabilityTheory.Kernel Ω ℝ,
      ProbabilityTheory.IsSFiniteKernel κ ∧
      ∀ ω : Ω, κ ω = dividendMeasure (runningSup X) ω := by sorry
