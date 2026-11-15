-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b126_original_zero_all_negative_counts_iff_true_jumpfree
-- name    : AvramDividend.Classical.avram_b126_original_zero_all_negative_counts_iff_true_jumpfree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:26:59.93222+00:00
-- url     : https://prove2.me/theorems/d98d598f-0ae1-4c02-a2d9-ad733a5d4967
-- title:
--   All original negative-mark Poisson cutoff counts vanish exactly when the physical source interval is genuinely jumpfree
-- statement:
--   On every sample path of the exact original spectrally negative Levy source and a genuine ordered half-open time interval, the original marked Poisson source measure assigns zero mass to every negative reciprocal cutoff rectangle if and only if the original physical process has zero jump increments at every time in the interval. The forward direction is the direct all-cutoff-to-physical B125 source theorem; the converse uses the actual jumpfree-to-original-Poisson B123 count theorem. This is a same-source equivalence for identifying all genuinely unmarked stopped-grid cells and passing to original compensated jump/Itô identities. It awaits proof of both imported source bridge theorems.
-- source:
--   Prepared original B125 and B123 proofs; publish after both Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
import Theorems.Thm_AvramDividend_Classical_avram_b123_original_actual_jumpfree_implies_every_negative_count_zero
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact original all-negative-cutoff Poisson zero count event is precisely physical jumpfree on any ordered half-open interval. -/

theorem AvramDividend.Classical.avram_b126_original_zero_all_negative_counts_iff_true_jumpfree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t) :
    (∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) ↔
    (∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0) := by sorry
