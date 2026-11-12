-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_past_atom_zero_case
-- name    : AvramDividend.Classical.avram_a06_original_cp_past_atom_zero_case
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:24:37.256691+00:00
-- url     : https://prove2.me/theorems/6cfd0f10-478a-4c2f-8388-0c43b9072987
-- title:
--   Original compound Poisson zero future count atom factors from all preceding count atoms
-- statement:
--   The no-arrival event on one original compound-Poisson time cell is independent of every finite preceding count-increment atom, under the original source driver; the residual survival factor is the mathematical core.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_past_atom_zero_case
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
      ∀ (j : Fin n) (v : Fin n → ℕ),
        P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = 0} =
          P {ω | ∀ i : Fin n, i < j → Z i ω = v i} *
          P {ω | Z j ω = 0} := by sorry
