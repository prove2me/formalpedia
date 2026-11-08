-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_e_arbitrary_shift_marked_loss
-- name    : AvramDividend.Classical.avram_route_runner_e_arbitrary_shift_marked_loss
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T16:38:38.998843+00:00
-- url     : https://prove2.me/theorems/935b151d-e59c-4f3d-bfb0-403a1e901f63
-- title:
--   Arbitrary original Lévy shifted marked loss equals the physical half-open cell loss
-- statement:
--   For every sample, deterministic shift s, duration T and strict negative cutoff k, the intrinsic weighted negative-jump loss over (0,T] for the genuine shifted future-increment path is exactly the physical original Lévy negative-jump loss over (s,s+T]. The proof uses the already proved arbitrary Borel marked rectangle count transport, measurable shifted mark map, and weighted rectangle measure integration theorem. It is the missing physical-to-future-path bridge for the equal-cell independence factorisation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_generic_measurable_mark_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_original_shifted_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_e_arbitrary_shift_marked_loss
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s T : ℝ≥0) (k : ℕ) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧
          (X.X (s + u) ω - X.X s ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          (X.X (s + u) ω - X.X s ω) -
            Function.leftLim
              (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u)))) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ s + T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0 ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
