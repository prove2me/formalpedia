-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
-- name    : AvramDividend.Classical.dividendMeasure_global_sfinite_kernel_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T23:32:40.061+00:00
-- url     : https://prove2.me/theorems/766b5129-2e5c-4d9d-a2db-12d0cca32e94
-- title:
--   Every adapted monotone dividend strategy induces a measurable s-finite random Stieltjes kernel on real time
-- statement:
--   For every adapted left-continuous monotone dividend strategy D, there exists an s-finite Markov kernel κ from sample paths to real dividend-payment times whose measure at each ω equals exactly the full Stieltjes measure dividendMeasure D ω. Partition real time into the disjoint integer unit intervals (n,n+1], restrict the dividend measure to each, use proved random interval-measure measurability and the finite interval mass lemma to show each interval kernel is s-finite, and sum them to recover the complete measure. This generalises the existing proved running-supremum-only kernel theorem and supplies the random-kernel construction needed for general truncated dividend-reward measurability.
-- source:
--   Adaptation of accepted AvramDividend.Classical.runningSup_dividendMeasure_global_sfinite_kernel_exists using proved dividendMeasure_restrict_Ioc_measurable and newly published dividendMeasure_Ioc_lt_top.

import Mathlib.Algebra.Order.ToIntervalMod
import Mathlib.Algebra.Order.Interval.Set.Group
import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Measure.Restrict
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_kernel_isSFinite_of_pointwise_finite
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_lt_top
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_restrict_Ioc_measurable
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_global_sfinite_kernel_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∃ κ : ProbabilityTheory.Kernel Ω ℝ,
      ProbabilityTheory.IsSFiniteKernel κ ∧
      ∀ ω : Ω, κ ω = dividendMeasure D ω := by sorry
