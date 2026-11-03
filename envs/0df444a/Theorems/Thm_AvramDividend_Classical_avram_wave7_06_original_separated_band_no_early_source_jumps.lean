-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_separated_band_no_early_source_jumps
-- name    : AvramDividend.Classical.avram_wave7_06_original_separated_band_no_early_source_jumps
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:40:47.072914+00:00
-- url     : https://prove2.me/theorems/f832b2ed-f173-4b2a-98a3-1923a215e3ac
-- title:
--   Actual original Lévy path has no separated-magnitude jumps sufficiently near time zero
-- statement:
--   For each genuine original sample path of a spectrally negative Lévy process and each integer threshold 1/(n+1), there is a strictly positive time interval after zero in which all left-limit jumps have strictly smaller magnitude. This follows pathwise from finiteness of jumps exceeding a fixed threshold on [0,1], and is a source-specific regularity lemma for the continuity-at-zero step of the genuine marked-void semigroup.
-- source:
--   Canonical original X, Ω and filtration, derived from Proved same-path finite-separated-jump theorem 52f0bc5f-fb6d-4e4c-95a7-20b6fc1c8835. W7-06 support for positive-horizon source-band Poisson void law aa265c9f-4568-4639-9694-5ab319ddc374; no auxiliary Poisson process or new stochastic assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_finite_horizon_separated_jump_marks_finite_every_path
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_separated_band_no_early_source_jumps
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (n : ℕ) :
    ∃ ε : ℝ≥0, 0 < ε ∧
      ∀ u : ℝ≥0, 0 < u → u < ε →
        dist (X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) 0 <
          1 / ((n : ℝ) + 1) := by sorry
