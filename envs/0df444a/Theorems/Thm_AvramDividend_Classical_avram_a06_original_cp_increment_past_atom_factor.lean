-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_increment_past_atom_factor
-- name    : AvramDividend.Classical.avram_a06_original_cp_increment_past_atom_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:43:13.511191+00:00
-- url     : https://prove2.me/theorems/441a8f25-9f79-467c-b2a0-182cb8727c56
-- title:
--   Original exponential renewal future count-increment atom factors from every preceding grid count cylinder
-- statement:
--   The substantive renewal-memoryless step: on the original compound Poisson driver and a fixed monotone finite horizon grid, any atom of the current count increment is independent of all previously specified count-increment atoms. This is the exact one-step probability content needed to telescope finite joint laws; finite-grid coordinate measurability is handled separately by the Proved 24563b34 theorem. The natural counting-history/future-exponential-suffix factorisation and a.e renewal threshold provide inputs. No new stochastic assumptions are added.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_increment_past_atom_factor
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
        P {ω | (∀ i : Fin n, i < j → Z i ω = v i) ∧ Z j ω = k} =
          P {ω | ∀ i : Fin n, i < j → Z i ω = v i} *
          P {ω | Z j ω = k} := by sorry
