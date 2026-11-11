-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_compoundPoisson_real_mgf
-- name    : AvramDividend.Classical.avram_a06_uniform_compoundPoisson_real_mgf
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:49:06.169607+00:00
-- url     : https://prove2.me/theorems/6dfbd74c-81e7-4ec3-b28a-d5f941078ac1
-- title:
--   Original source compound-Poisson uniform-mark real moment-generating identity
-- statement:
--   For the original rate-one compound-Poisson source with negative uniform marks, compute the real exponential moment using the joint Poisson count and i.i.d. mark laws.
-- source:
--   A06 original source-exact compensated Laplace transform identity; independent of generator algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_uniform_compoundPoisson_real_mgf
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ *
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) ∂P) =
      Real.exp ((t : ℝ) * (θ + (∫ y in Ioo (-1 : ℝ) 0,
      (Real.exp (θ * y) - 1) ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))))) := by sorry
