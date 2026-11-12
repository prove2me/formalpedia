-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_past_atom_positive_case
-- name    : AvramDividend.Classical.avram_a06_original_cp_past_atom_positive_case
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:24:47.115612+00:00
-- url     : https://prove2.me/theorems/08309422-9809-48a8-a98d-f7f55304ca67
-- title:
--   Original compound Poisson positive future count atom factors from all preceding count atoms
-- statement:
--   For every k, the event of k+1 arrivals on one original compound-Poisson time cell is independent of every finite preceding count-increment atom, under the original source driver; its proof uses residual waiting time plus future interarrival suffix.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_past_atom_positive_case
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      let Z : Fin n → ((ℕ → ℝ) × (ℕ → ℝ)) → ℕ :=
        fun i ω => LevyFoundations.jumpCount
          (fun q => LevyFoundations.arrival τ q ω) (t i.succ : ℝ) -
        LevyFoundations.jumpCount
          (fun q => LevyFoundations.arrival τ q ω) (t i.castSucc : ℝ)
      ∀ (j : Fin n) (v : Fin n → ℕ) (k : ℕ),
        P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = k + 1} =
          P {ω | ∀ i : Fin n, i < j → Z i ω = v i} *
          P {ω | Z j ω = k + 1} := by sorry
