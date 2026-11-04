-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:19:50.09371+00:00
-- url     : https://prove2.me/theorems/54643412-7eb2-4fdf-8178-97b28f1ab720
-- title:
--   Original BV source raw real negative-left-jump series has absolutely summable magnitudes
-- statement:
--   For every ordered finite observation interval of the genuine original BV spectrally negative Lévy process, the raw real left-jump sum is absolutely summable almost surely, simultaneously over all intervals. This supplies the exact summable envelope for dominated-convergence and left-limit proofs without a Poisson representation.
-- source:
--   Proved f0ec726b actual original interval raw real jump summability, Mathlib Summable.abs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_raw_negative_jump_real_tsum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Every original BV bounded-interval raw real negative-jump series
is absolutely summable, ready for Tannery dominated convergence. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      Summable (fun u : ℝ≥0 =>
        |if s < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0|) := by sorry
