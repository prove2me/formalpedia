-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_marked_band_count_law_transfer
-- name    : AvramDividend.Classical.avram_a06_original_marked_band_count_law_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:58:41.323207+00:00
-- url     : https://prove2.me/theorems/7dae9fbf-9643-438c-ae8d-b44389eeff42
-- title:
--   Original Poisson count stationary law transports fresh-mark sums to the interval from zero
-- statement:
--   For the actual original compound-Poisson driver, the prefix marked sum with random length equal to the count increment from s to s+k has the law of the marked band from 0 to k. This isolates stationary renewal count law plus source-exact count/mark independence and the zero-time count boundary.
-- source:
--   Prove stationary law of original exponential-renewal jumpCount increments; compose its law with original iid mark stream independent of the full count process, then identify N_0=0 almost surely. Reuse the proved original full count-vector/mark-stream independence and finite-block shift.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_marked_band_count_law_transfer
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s k : ℝ≥0) :
    IdentDistrib
      (fun ω => ∑ j ∈ Finset.range ((LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s + k : ℝ)) - (LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (s : ℝ))), Y j ω)
      (fun ω => ∑ j ∈ Finset.Ico (LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (0 : ℝ)) (LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (k : ℝ)), Y j ω) P P := by sorry
