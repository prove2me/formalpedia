-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_marked_band_random_index_shift
-- name    : AvramDividend.Classical.avram_a06_original_marked_band_random_index_shift
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T02:58:38.850211+00:00
-- url     : https://prove2.me/theorems/62a946d6-f6a0-4695-8852-e473a29a82ac
-- title:
--   Original Poisson marked jump band equals its fresh-mark random-length block in distribution
-- statement:
--   For the actual original compound-Poisson driver, a marked sum whose starting index is the random count up to s has the same law as a fresh-prefix marked sum of the same random count increment length. Count vectors are independent of all marks, and original iid marks are invariant under shifts. This isolates the random-index mark conditional-law step required for A06 stationary increments.
-- source:
--   Condition on the count-vector (N_s,N_(s+k)); the proved original count-vector/full-mark-stream independence yields a common mark product law. Shift the iid mark sequence by the realised N_s. Reindex the finite interval sum via sum_Ico_eq_sum_range; justify conditional countable sum and measurability. Reuse Proved 2a404e7e and 75627888.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_marked_band_random_index_shift
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.Ico (LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s : ℝ)) (LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ)), Y j ω)
      (fun ω => ∑ j ∈ Finset.range ((LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ)) - (LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s : ℝ))), Y j ω) P P := by sorry
