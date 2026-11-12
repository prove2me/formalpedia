-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_smallband_cutoff_centered
-- name    : AvramDividend.Classical.avram_ja21_original_smallband_cutoff_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T15:11:06.032474+00:00
-- url     : https://prove2.me/theorems/1ff51093-76fc-47e8-9d1d-c74f9cb15000
-- title:
--   Original compensated small-jump cutoff is centred under physical measure
-- statement:
--   Prove zero expectation of the compensated n-th original negative small jump band, using source compensator and finite-activity first moments, with no large-mark first-moment assumptions.
-- source:
--   J-A21 reduction of original physical independence/centring d57f06bf feeding root-connected 1e8c653a and 10ff2b5a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_smallband_cutoff_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (-avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ∂P) = 0 := by sorry
