-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_consecutive_centered_increment_cross_moment_zero
-- name    : AvramDividend.Classical.avram_wave7_06_original_consecutive_centered_increment_cross_moment_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:30:09.320351+00:00
-- url     : https://prove2.me/theorems/1e46eb9d-0b63-4311-b7b1-af1760a2908c
-- title:
--   Original consecutive zero-mean increments have vanishing mixed first-order L² cross moment
-- statement:
--   On the original Levy probability space, if two consecutive source increments are integrable and individually centred, independence implies that their mixed expected product is zero. The conclusion is source-specific, and the two centring hypotheses are stated explicitly rather than imposed without proof.
-- source:
--   W7-06 raw original source consecutive orthogonality precursor to marked compensated L² isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_consecutive_centered_increment_cross_moment_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (hFirst : Integrable (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable (fun ω =>
      X.X (s + u + v) ω - X.X (s + u) ω) P)
    (hZeroFirst : (∫ ω, X.X (s + u) ω - X.X s ω ∂P) = 0)
    (hZeroSecond :
      (∫ ω, X.X (s + u + v) ω - X.X (s + u) ω ∂P) = 0) :
    (∫ ω, (X.X (s + u) ω - X.X s ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω) ∂P) = 0 := by sorry
