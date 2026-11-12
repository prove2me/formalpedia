-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_increment_step_atom_factor
-- name    : AvramDividend.Classical.avram_a06_original_cp_increment_step_atom_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:31:13.718462+00:00
-- url     : https://prove2.me/theorems/c31910ed-fd91-427b-90b2-663a0e319950
-- title:
--   Original unit-exponential count increment atom is independent of prior count-increment cylinders
-- statement:
--   For any finite ordered deterministic grid on the exact original exponential-interarrival driver, the next count increment's singleton event factorises from any joint cylinder event involving earlier count increments. Earlier-grid cylinders are measurable in the full counting history, while the next increment is a function of the residual exponential wait and entire future exponential stream; proved natural-history/future factorisation and count-increment thresholds supply the underlying renewal argument. The child also includes measurability of increment coordinates.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_increment_step_atom_factor
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
      (∀ i, Measurable (Z i)) ∧
      ∀ (j : Fin n) (v : Fin n → ℕ) (k : ℕ),
        P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = k} =
          P {ω | ∀ i : Fin n, i < j → Z i ω = v i} *
          P {ω | Z j ω = k} := by sorry
