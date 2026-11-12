-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_residual_stream_identDistrib
-- name    : AvramDividend.Classical.avram_a06_original_cp_residual_stream_identDistrib
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T08:11:33.250241+00:00
-- url     : https://prove2.me/theorems/cf142046-a9a7-43c6-b83c-714340dcac3d
-- title:
--   Original compound-Poisson residual waiting-time and entire future stream retain the full iid exponential law
-- statement:
--   For the original same-space rate-one compound-Poisson driver and each fixed nonnegative time s, the selected residual interarrival time followed by every future interarrival time, as a complete infinite stream, has the same distribution as the original independent exponential interarrival stream.
-- source:
--   From proved chat06_random_count_residual_full_future_joint_from_threshold, show equality on first-coordinate upper rays crossed with measurable infinite-suffix cylinders, extend to the Borel sigma-algebra of ℝ × (ℕ→ℝ) by uniqueness, and transport across the first-tail stream equivalence. This uses the original τ on its original probability measure.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_residual_stream_identDistrib
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (s : ℝ≥0) :
    IdentDistrib
      (fun ω (j : ℕ) =>
        if j = 0 then
          τ (LevyFoundations.jumpCount
            (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)) ω -
          ((s : ℝ) - ∑ i ∈ Finset.range
            (LevyFoundations.jumpCount
              (fun i => LevyFoundations.arrival τ i ω) (s : ℝ)), τ i ω)
        else
          τ (LevyFoundations.jumpCount
            (fun i => LevyFoundations.arrival τ i ω) (s : ℝ) + j) ω)
      (fun ω j => τ j ω) P P := by sorry
