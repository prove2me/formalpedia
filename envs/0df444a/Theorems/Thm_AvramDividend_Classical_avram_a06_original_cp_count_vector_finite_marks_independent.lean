-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_vector_finite_marks_independent
-- name    : AvramDividend.Classical.avram_a06_original_cp_count_vector_finite_marks_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T03:02:26.860561+00:00
-- url     : https://prove2.me/theorems/8efaf877-3826-4c09-a261-7d7ecd6b4736
-- title:
--   Original Poisson count vector is independent of any fixed finite shifted mark sum
-- statement:
--   The original count vector at arbitrary finitely many times is independent of every fixed shifted finite-block sum of original marks. This is the fixed-block independence ingredient for removing random starting indices in marked jump-band stationarity.
-- source:
--   From Proved 2a404e7e, compose the right-hand entire mark stream with the measurable finite-block sum. Use Finset.measurable_sum and measurable_pi_apply, and IndepFun.comp with measurable_id.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_vector_mark_independent
open MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_count_vector_finite_marks_independent
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (n : ℕ) (t : Fin n → ℝ≥0) (m ℓ : ℕ) :
    IndepFun
      (fun ω (i : Fin n) => LevyFoundations.jumpCount
        (fun j => LevyFoundations.arrival τ j ω) (t i : ℝ))
      (fun ω => ∑ j ∈ Finset.range ℓ, Y (m + j) ω) P := by sorry
