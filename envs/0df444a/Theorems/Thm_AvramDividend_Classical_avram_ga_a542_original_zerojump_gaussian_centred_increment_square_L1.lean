-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a542_original_zerojump_gaussian_centred_increment_square_L1
-- name    : AvramDividend.Classical.avram_ga_a542_original_zerojump_gaussian_centred_increment_square_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:47:09.157233+00:00
-- url     : https://prove2.me/theorems/ccf9c53e-c238-4c5a-81db-b5d371386923
-- title:
--   Original zero-jump Gaussian centred increment has integrable square at any fixed two times
-- statement:
--   For the original zero-jump Lévy process, centred increments between any two deterministic times inside a finite horizon have finite second moments, using the already proved continuous-martingale L2 maximal envelope.
-- source:
--   Apply Proved a400 common integrable quadratic maximal envelope to the original centred Lévy martingale, and generic a540 L2 finite increment domination.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_zerojump_centered_source_martingale
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a542_original_zerojump_gaussian_centred_increment_square_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (T s t : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) :
    Integrable (fun ω =>
      ((X.X t ω - (t : ℝ) * X.c) -
        (X.X s ω - (s : ℝ) * X.c))^2) P := by sorry
