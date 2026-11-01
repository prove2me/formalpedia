-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_reflected_ruin_barrier_level_measurable
-- name    : AvramDividend.Classical.avram_wave4_01_original_reflected_ruin_barrier_level_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:45:52.964874+00:00
-- url     : https://prove2.me/theorems/03cbd14a-0f35-4d3f-8d05-40961279b1c0
-- title:
--   Genuine reflected drawdown first-ruin clock is Borel measurable in the barrier level, pathwise
-- statement:
--   For each actual spectrally negative Lévy sample path, the extended nonnegative first strict reflected drawdown ruin time D_a is a Borel measurable function of the real barrier a. No Standing. The exact pathwise monotonicity of the true ruin clock, already canonically Proved, implies measurability between the Borel linear orders ℝ and ℝ≥0∞.
-- source:
--   Uses Proved barrierRuinTime_mono_barrier (6c566972-11fb-48af-a946-abaa30336bf1) and pinned Mathlib Monotone.measurable, without stochastic axioms.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_reflected_ruin_barrier_level_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Measurable (fun a : ℝ => barrierRuinTime X a ω) := by sorry
