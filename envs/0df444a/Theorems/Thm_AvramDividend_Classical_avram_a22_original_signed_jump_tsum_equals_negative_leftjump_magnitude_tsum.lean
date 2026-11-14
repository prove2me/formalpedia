-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_signed_jump_tsum_equals_negative_leftjump_magnitude_tsum
-- name    : AvramDividend.Classical.avram_a22_original_signed_jump_tsum_equals_negative_leftjump_magnitude_tsum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:47:13.814913+00:00
-- url     : https://prove2.me/theorems/c5765f5b-6f3a-46fe-bb53-8ff23fd6d812
-- title:
--   Original signed physical jump-time tsum is the negative of the original left-jump magnitude tsum
-- statement:
--   At every horizon and on every actual sample path of the original Lévy process, reversing each left-limit jump difference reverses the sum of all actual leftjump contributions over (0,t]. This exact pointwise algebra holds with original source path, no auxiliary probability or finite-activity assumption, using the Mathlib real tsum-neg identity. It bridges raw original marked signed jump sums with the BV drift physical downward jump series.
-- source:
--   Original actual physical jump path definition, Mathlib tsum_neg; Proved a55466fc finite support guarantees finite sums in the source application.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_signed_jump_tsum_equals_negative_leftjump_magnitude_tsum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (t : ℝ≥0) :
    (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u else 0) =
    -(∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u - X.X u ω else 0) := by sorry
