-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_intrinsic_gaussian_core_indep_smallband
-- name    : AvramDividend.Classical.avram_ja21_original_intrinsic_gaussian_core_indep_smallband
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T15:10:54.063327+00:00
-- url     : https://prove2.me/theorems/7955f9bd-1393-4266-af54-42c400845564
-- title:
--   Original Gaussian continuous core is independent of its compensated physical small-jump cutoff
-- statement:
--   Prove independence of the continuous original Gaussian component and the compensated jump cutoff on the original Ω,P,𝓕 via Levy-Ito/noise orthogonality, without an unproved auxiliary Brownian identification.
-- source:
--   J-A21 reduction of original physical independence/centring d57f06bf feeding root-connected 1e8c653a and 10ff2b5a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_intrinsic_gaussian_core_indep_smallband
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      ProbabilityTheory.IndepFun (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω + avram_p4_h_gaussian_intrinsic_small_band_compensated X 0 t ω)) (fun ω => (-avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω)) P := by sorry
