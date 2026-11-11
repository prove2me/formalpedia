-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_cp_fixed_mark_real_moment
-- name    : AvramDividend.Classical.avram_a06_original_cp_fixed_mark_real_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T19:37:58.220549+00:00
-- url     : https://prove2.me/theorems/8e3989b8-49ab-4041-81cf-13ef95bd5e06
-- title:
--   Fixed-count exponential moment of original uniform negative marks
-- statement:
--   The original independent identically distributed negative marks have a finite exponential moment, and the moment of their fixed-length sum is the corresponding one-mark moment raised to that length.
-- source:
--   Required finite-mark factorisation in the Proved real random-sum Laplace theorem, using the actual original driver and uniform mark law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
open MeasureTheory ProbabilityTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_cp_fixed_mark_real_moment
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) (k : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * ∑ i ∈ Finset.range k, Y i ω) ∂P) =
      (∫ y, Real.exp (θ * y) ∂
        ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))) ^ k := by sorry
