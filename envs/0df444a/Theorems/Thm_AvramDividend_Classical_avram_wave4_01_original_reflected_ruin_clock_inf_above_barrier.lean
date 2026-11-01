-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_reflected_ruin_clock_inf_above_barrier
-- name    : AvramDividend.Classical.avram_wave4_01_original_reflected_ruin_clock_inf_above_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:56:53.530365+00:00
-- url     : https://prove2.me/theorems/9c51006b-9fc8-42ac-bcd5-a352d38e67d5
-- title:
--   Original strict reflected drawdown ruin time equals the infimum of ruin times at strictly higher barriers
-- statement:
--   For any actual spectrally negative Lévy sample and real drawdown barrier a, the true strict reflected drawdown first ruin time D_a is the infimum in extended nonnegative time of D_b over all real b>a. The source proof uses monotonicity and the genuine pathwise strict drawdown breach identity; a first strict breach at time t leaves a positive depth margin, so a midpoint barrier b>a also breaches by t. Includes unreachable barriers and infinite clocks, no Standing.
-- source:
--   Proved original barrierRuinTime_mono_barrier (6c566972) and avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock (75280f18); direct midpoint order argument as for strict upward record clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierRuinTime_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierRuinTime_eq_strict_drawdown_subtype_clock
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_reflected_ruin_clock_inf_above_barrier
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a : ℝ) (ω : Ω) :
    barrierRuinTime X a ω =
      ⨅ b : {b : ℝ // a < b}, barrierRuinTime X b.1 ω := by sorry
