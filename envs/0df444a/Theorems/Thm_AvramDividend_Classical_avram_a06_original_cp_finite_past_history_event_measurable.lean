-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_finite_past_history_event_measurable
-- name    : AvramDividend.Classical.avram_a06_original_cp_finite_past_history_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:56:45.562705+00:00
-- url     : https://prove2.me/theorems/21396273-7c34-44c4-a697-5c1440be49c9
-- title:
--   Original compound Poisson finite past-count event ordinary and history measurability
-- statement:
--   Every finite grid prefix count-atom is measurable both in the underlying sample sigma algebra and in the count-history sigma algebra up to the left endpoint. This isolates the deterministic Fin-index and comap-measurability reasoning from the exponential renewal independence argument.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_finite_grid_count_increment_measurable
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_finite_past_history_event_measurable
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ))) [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) :
    ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t)
      (j : Fin n) (v : Fin n → ℕ),
      let N (ω : (ℕ → ℝ) × (ℕ → ℝ)) (u : ℝ) :=
        LevyFoundations.jumpCount (fun q => LevyFoundations.arrival τ q ω) u
      let clock : ℝ := t j.castSucc
      let H : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
        {ω | ∀ i : Fin n, i < j →
          N ω (t i.succ : ℝ) - N ω (t i.castSucc : ℝ) = v i}
      MeasurableSet H ∧
        MeasurableSet[
          MeasurableSpace.comap
            (fun ω : (ℕ → ℝ) × (ℕ → ℝ) =>
              fun s : Set.Iic clock => N ω (s : ℝ))
            (inferInstance : MeasurableSpace (Set.Iic clock → ℕ))] H := by sorry
