-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_increment_joint_atomic_product
-- name    : AvramDividend.Classical.avram_a06_original_cp_count_increment_joint_atomic_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:16:40.672758+00:00
-- url     : https://prove2.me/theorems/a1996da4-748a-425f-9ac5-2804bb195d9d
-- title:
--   Original exponential renewal count increments have factorised finite joint atomic probabilities
-- statement:
--   On the exact same probability space of the original iid unit-exponential compound-Poisson driver, every deterministic ordered finite-grid count increment has a measurable natural-valued law and the probability of each joint count-increment cylinder is the product of its marginal atomic probabilities. This is the substantive renewal/Poisson calculation; previous Proved one-cell laws and residual-future lemmas supply its probability ingredients.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_count_increment_joint_atomic_product
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t),
      (∀ i : Fin n, Measurable (fun ω =>
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
        LevyFoundations.jumpCount
          (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ))) ∧
      ∀ v : Fin n → ℕ,
        P {ω | ∀ i : Fin n,
          (LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
           LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)) = v i} =
        ∏ i : Fin n, P {ω |
          (LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.succ : ℝ) -
           LevyFoundations.jumpCount
            (fun k => LevyFoundations.arrival τ k ω) (t i.castSucc : ℝ)) = v i} := by sorry
