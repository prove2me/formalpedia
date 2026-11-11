-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_count_vector_mark_independent
-- name    : AvramDividend.Classical.avram_a06_original_cp_count_vector_mark_independent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T02:07:00.0966+00:00
-- url     : https://prove2.me/theorems/2a404e7e-da36-4488-9005-5f3cd58ce25e
-- title:
--   Original compound-Poisson finite arrival-count vectors are independent of all jump marks
-- statement:
--   For an original marked compound-Poisson driver, every finite vector of counting-process values at deterministic times is independent of the entire sequence of marks. This joint independence is needed for the root-connected A06 stationary and independent marked-band sum laws.
-- source:
--   Generalise Proved A06 original single-count mark independence (0ccf775e) by composing the independent interarrival-coordinate stream with a finite measurable count-vector map. A genuine source-exact ingredient of the two still Open A06 marked-band increment laws.

import Mathlib
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Theorems.Thm_levy_foundations_iIndepFun_setRestrict_pairwiseDisjoint
import Theorems.Thm_AvramDividend_Classical_avram_a06_compound_jumpCount_measurable_public
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_count_vector_mark_independent
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P)
    (n : ℕ) (t : Fin n → ℝ≥0) :
    IndepFun (fun ω (i : Fin n) => LevyFoundations.jumpCount
      (fun j => LevyFoundations.arrival τ j ω) (t i : ℝ))
      (fun ω (j : ℕ) => Y j ω) P := by sorry
