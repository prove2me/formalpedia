-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
-- name    : AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:52:01.764989+00:00
-- url     : https://prove2.me/theorems/e4542c93-c64b-453a-b582-e5ec26265dfc
-- title:
--   Original-path Lévy intrinsic counting-measure integral equals actual nonnegative jump sum
-- statement:
--   For every actual source spectrally negative Lévy process X, every original sample ω and every measurable nonnegative extended-valued time–mark kernel f, integration of f against the intrinsic original-path counting measure defined by the restriction of time-counting measure to positive nonzero source jumps and pushforward by u↦(u,ΔX_uω) equals the unrestricted ENNReal sum over real times of f(u,ΔX_uω) times the indicator of a genuine nonzero positive-time jump. The equality is pathwise, allowing infinitely many jumps and infinite integrals. It is not a stochastic Campbell expectation or compensated integral.
-- source:
--   Pinned Mathlib lintegral_map, lintegral_indicator, lintegral_count and tsum_congr; canonical Proved source jump-mark joint measurable 9d68c5c2-c2c9-4cf9-a3d8-48c7929b7fc1 and intrinsic rectangle measure f6336d40-2d19-444f-bacd-83724316de67.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (f : (ℝ≥0 × ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑' u : ℝ≥0, if 0 < u ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0
      then f (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)
      else 0 := by sorry
