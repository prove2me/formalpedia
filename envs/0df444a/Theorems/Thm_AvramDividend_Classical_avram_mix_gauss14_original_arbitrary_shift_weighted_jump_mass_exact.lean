-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
-- name    : AvramDividend.Classical.avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T10:53:33.754579+00:00
-- url     : https://prove2.me/theorems/3bf3911b-78b0-41dc-bdb2-cfd363bf7d15
-- title:
--   Original weighted jump mass on a future interval equals the Borel marked mass of its actual shifted path
-- statement:
--   For the actual original SpectrallyNegativeLevy process, arbitrary deterministic shift s, horizon T and nonnegative Borel mark weight g, identify exactly the marked jump lintegral over the future window (s,s+T] of the original path with the marked jump lintegral over (0,T] of the actual shifted increment path. Derive rectangle equality from Proved b1721778 future path count transport and generic marked rectangle encard, using the proved shift mark-map measurability, then lift all Borel weights by 68109213. This supplies the shift-covariance requirement for transferring original shifted-path filtration independence to actual Gaussian residual jump increments without an auxiliary process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_weighted_mark_lintegral_of_rectangle_equality
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_generic_measurable_mark_rectangle_encard
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_original_shifted_mark_map_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_gauss14_original_arbitrary_shift_weighted_jump_mass_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s T : ℝ≥0) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ (X.X (s + u) ω - X.X s ω) -
          Function.leftLim (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, (X.X (s + u) ω - X.X s ω) -
          Function.leftLim (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω) u)))) =
    (∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ s + T then g p.2 else 0 ∂
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) := by sorry
