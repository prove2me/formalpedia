-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_negative_borel_mark_unconditional_levy_rate
-- name    : AvramDividend.Classical.avram_wave7_01_original_intrinsic_negative_borel_mark_unconditional_levy_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:30:59.741741+00:00
-- url     : https://prove2.me/theorems/4928a464-057d-4fd0-a2c0-099e206d3a21
-- title:
--   Exact unconditional original Lévy jump intensity for arbitrary strictly negative Borel mark bands
-- statement:
--   For the actual original spectrally negative Lévy process and any Borel B wholly contained in (-∞,0), prove that the expected literal jump count on (s,t]×B is (t−s)ν(B). This is the remaining Lévy–Itô mark-intensity identification without BV, finite activity, a replacement Poisson sample space or a conditional compensator assumption. Once proved, original-path negative support and ν support extend it to every Borel mark set.
-- source:
--   Actual source σ-finite expected marked occupation measure e509ef60, small-time exponential moment derivative e6973988, Borel marked grid first moments 20fc3267 and source jump-band monotone exhaustion. The theorem remains Open pending Lévy–Khintchine measure identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_jump_rectangle_restrict_to_strictly_negative_marks

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_intrinsic_negative_borel_mark_unconditional_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
