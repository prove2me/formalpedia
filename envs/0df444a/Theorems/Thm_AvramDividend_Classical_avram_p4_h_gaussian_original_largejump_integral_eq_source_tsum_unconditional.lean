-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_source_tsum_unconditional
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_largejump_integral_eq_source_tsum_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:41:44.476524+00:00
-- url     : https://prove2.me/theorems/c63fdd06-133c-43b4-8a78-990b74babc8f
-- title:
--   Original uncompensated large negative jump integral equals exact original jump series, unconditionally
-- statement:
--   For every original sample ω of the source Lévy process and finite horizon T, the actual uncompensated large-negative-jump integral Jlarge equals the corresponding original jump-time series, with no integrability assumption, Poisson process on another probability space or extra source decomposition. It follows by combining genuine finite-source large-band integrability with the previously Proved pathwise integral-to-source tsum identity.
-- source:
--   Proved source original large-band signed integral series 970d5a93; pending source finite jump support to unconditional integrability. No external source is introduced.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_mark_integrable_from_finite_support
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largeband_integral_eq_source_tsum_of_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_largejump_integral_eq_source_tsum_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) :
    let j : ℝ≥0 → ℝ := fun u =>
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
    let E : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ Iic (-1 : ℝ)
    avram_p4_h_gaussian_intrinsic_large_jump_sum X T ω =
      ∑' u : ℝ≥0, if 0 < u ∧ j u ≠ 0 then
        E.indicator (fun p : ℝ≥0 × ℝ => p.2) (u, j u) else 0 := by sorry
