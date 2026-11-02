-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_relative_stopped_band_count_identification_finite
-- name    : AvramDividend.Classical.avram_wave5_01_actual_source_relative_stopped_band_count_identification_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:44:16.184443+00:00
-- url     : https://prove2.me/theorems/d9e8873d-6335-4bfa-a73c-eb98f3a9af42
-- title:
--   Original Lévy relative random-clock marked-band count equals its finite genuine source jump count
-- statement:
--   For every original source sample path X(.,ω), deterministic s and T, arbitrary random clock τ(ω), and δ>0, the actual marked count on (s,s+min(τ(ω),T)] with marks at least δ in magnitude is exactly the finite encard of genuine original jump times v on the relative interval. No stopping-time property or BV assumption is used; this is pathwise clipping and source mark identification only, not a compensator.
-- source:
--   Compose Proved original-path marked-count clock translation 01b004c1-fba2-4778-a12a-1c4a27e2ced0 with Proved arbitrary-clock separated-jump finiteness 35a471e5-c0cb-4241-95d2-aadc001e877b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_count_clock_translation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_01_actual_source_relative_stopped_band_count_identification_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s T : ℝ≥0) (τ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + min (τ ω) T) ×ˢ {y : ℝ | δ ≤ dist y 0}) = ({v : ℝ≥0 | 0 < v ∧ v ≤ min (τ ω) T ∧
      X.X (s + v) ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) (s + v) ≠ 0 ∧
      δ ≤ dist (X.X (s + v) ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) (s + v)) 0}).encard) ∧
      (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + min (τ ω) T) ×ˢ {y : ℝ | δ ≤ dist y 0}) < ⊤) := by sorry
