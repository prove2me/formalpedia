-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:21:26.828211+00:00
-- url     : https://prove2.me/theorems/35a471e5-c0cb-4241-95d2-aadc001e877b
-- title:
--   Actual original marked jump count finite under arbitrary random-clock clipping on a finite horizon
-- statement:
--   For the actual SpectrallyNegativeLevy P 𝓕, every original ω, deterministic start s and horizon T, arbitrary random time map τ:Ω→ℝ≥0, and δ>0, the literal marked source jump count on (s,min(τ(ω),T)]×{y:|y|≥δ} is finite. It is an unconditional pathwise stopped localisation; no stopping-time measurability, BV, finite activity, detached process, or intensity assumptions are required. It supplies the exact original measure at random-clipped finite horizons used in stochastic compensation and controlled Ito-Meyer truncations.
-- source:
--   Monotonicity of the genuine marked source counting measure and the Proved original every-path finite-horizon separated band count UUID 557aabfa-c990-4bdc-9eff-492f4477acbf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_original_marked_jump_count_finite_on_separated_band_every_path
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s T : ℝ≥0) (τ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (min (τ ω) T) ×ˢ {y : ℝ | δ ≤ dist y 0}) < ⊤ := by sorry
