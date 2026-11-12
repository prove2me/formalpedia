-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_residual_stream_source_bridge
-- name    : AvramDividend.Classical.avram_a06_original_cp_residual_stream_source_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:00:01.186507+00:00
-- url     : https://prove2.me/theorems/f7945821-0fba-4a35-b7aa-81c06584a13e
-- title:
--   Original physical residual waiting-time stream distribution bridge
-- statement:
--   The complete residual interarrival stream from the original compound-Poisson process has the same law as the original iid exponential waiting-time stream. Derived from the already Proved original physical rectangle identity, strict residual positivity, joint measurability and measurable stream reassembly.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_residual_stream_source_bridge
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
