-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_disjoint_count_increments_independent
-- name    : AvramDividend.Classical.avram_a06_original_cp_disjoint_count_increments_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:40:29.232586+00:00
-- url     : https://prove2.me/theorems/721f460c-69da-45ee-ad68-c225b74724df
-- title:
--   Original unit-exponential compound-Poisson count increments over disjoint deterministic bands are independent
-- statement:
--   On the exact original product probability space of the unit-rate exponential and negative uniform mark driver, every finite monotone deterministic time grid yields an independent family of nonnegative arrival-count increments. This is a genuine count-process independent-increment obligation needed for the original marked-band independence theorem 2a80927e, beyond the already Proved single-cell stationary count law.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_disjoint_count_increments_independent
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      iIndepFun (fun (i : Fin n) ω =>
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)) P := by sorry
