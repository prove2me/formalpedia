-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
-- name    : AvramDividend.Classical.avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:39:11.296408+00:00
-- url     : https://prove2.me/theorems/be9b7fea-024d-4c8f-a424-03a3a4fddcaf
-- title:
--   Genuine original full negative marked Poisson count up to any measurable random physical horizon is measurable
-- statement:
--   For the original spectrally negative Lévy process and any measurable possibly random physical time horizon, the original marked jump Poisson counting measure evaluated over the stopped half-open time interval crossed with all strictly negative marks is a measurable extended nonnegative real random variable. Proved jump_phys13 makes the original negative reciprocal cutoff band counts on the same genuine random interval measurable for every cutoff index. Prepared B197 proves that on every actual original sample path, these counts converge as the cutoff grows to the complete negative marked source count, using monotone marked measure continuity from below and cutoff band exhaustion. The remotely signature-verified Mathlib ENNReal.measurable_of_tendsto theorem transfers measurable finite-cutoff source count functions to their pointwise limit via tendsto_pi_nhds. This source-specific measurable full negative Poisson count is the missing hypothesis in prepared B195, and together with Proved original mix_fin14 finite expected source count gives conull finite-negative-jump activity on the true original random horizon without imposing all-path finiteness or replacing the stochastic source. Publish after B197 Proved.
-- source:
--   Proved original jump_phys13 random-clock negative band source measurable; prepared B197 exact marked source measure continuity; remotely verified ENNReal.measurable_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_jump_phys13_original_random_interval_negative_cutoff_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_b197_negative_cutoff_marked_measure_mass_tendsto_full_negative
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual original complete negative-jump Poisson count on a bounded measurable random physical clock interval is a measurable ENNReal random variable. -/

theorem AvramDividend.Classical.avram_b198_original_fullnegative_bounded_random_clock_poisson_count_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (σ : Ω → ℝ≥0) (hσ : Measurable σ) :
    Measurable (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ))) := by sorry
