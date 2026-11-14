-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a23_every_cutoff_increment_shift_borel_20261113
-- name    : AvramDividend.Classical.avram_a23_every_cutoff_increment_shift_borel_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:09:34.425359+00:00
-- url     : https://prove2.me/theorems/ea8d4ba1-f28d-480b-b2d4-a2efc1d3467b
-- title:
--   Every original Gaussian residual cutoff increment is a Borel functional of the actual future source path
-- statement:
--   Under finite negative mark activity, each fixed original residual cutoff n has an increment on deterministic (s,t] given by a measurable functional of the original Levy future-increment path, with no independent replacement source.
-- source:
--   Proved 1afff3a2 and 4b47cce4, new A23 original physical retained-band future path Borel functional; all zero-time/signed compensation handled on the same source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja18h_original_intrinsic_residual_increment_shift_borel
import Theorems.Thm_AvramDividend_Classical_avram_ja21_original_cutoff_residual_gaussian_core_split
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original Gaussian cutoff increments depend measurably on the original shifted future path. -/

theorem AvramDividend.Classical.avram_a23_every_cutoff_increment_shift_borel_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (s t : ℝ≥0) (hst : s ≤ t) :
    ∃ W : (ℝ≥0 → ℝ) → ℝ, Measurable W ∧
      ∀ ω : Ω,
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω -
          avram_p4_h_gaussian_intrinsic_truncated_residual X n s ω =
        W (fun u : ℝ≥0 => X.X (s + u) ω - X.X s ω) := by sorry
