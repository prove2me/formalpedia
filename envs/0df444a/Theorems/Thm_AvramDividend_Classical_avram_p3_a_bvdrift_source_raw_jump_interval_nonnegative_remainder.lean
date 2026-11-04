-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_source_raw_jump_interval_nonnegative_remainder
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_source_raw_jump_interval_nonnegative_remainder
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:51:39.276914+00:00
-- url     : https://prove2.me/theorems/46850ddf-12e0-4cba-87a8-dbb185492ee8
-- title:
--   Actual BV original raw real left-jump series has a nonnegative source drift remainder on every interval
-- statement:
--   Under the original BV spectrally negative Lévy process, the actual signed real negative-left-jump sum on each sample-path interval is summable and is complemented by a nonnegative real residual to yield the physical drift-minus-source-process increment. This is a source-driven finite variation budget, without any assumption that the residual vanishes.
-- source:
--   Existing Proved source interval nonnegative remainder e84d1832 and true-source real jump summability and equality f0ec726b; no independent process representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The genuine BV raw signed real left-jump series, rather than merely its
nonnegative ENNReal encoding, enters the canonical drift increment with a
nonnegative residual on every original sample-path interval. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_source_raw_jump_interval_nonnegative_remainder
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      ∃ r : ℝ, 0 ≤ r ∧
        (∑' (u : ℝ≥0),
          if s < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
          else 0) + r =
        (((t : ℝ) * X.drift - X.X t ω) -
          ((s : ℝ) * X.drift - X.X s ω)) := by sorry
