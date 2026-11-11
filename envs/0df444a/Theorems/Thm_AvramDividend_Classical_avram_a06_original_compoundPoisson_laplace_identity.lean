-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_compoundPoisson_laplace_identity
-- name    : AvramDividend.Classical.avram_a06_original_compoundPoisson_laplace_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:27:28.131243+00:00
-- url     : https://prove2.me/theorems/166c8eff-8098-4ceb-bac6-81e6911221cf
-- title:
--   Original compound-Poisson uniform negative marks have the exact compensated Laplace transform
-- statement:
--   For the original unit-rate compound-Poisson process with uniform negative marks, evaluate the nonnegative-frequency exponential moment exactly as the exponent of the drift-one compensated Lévy generator. Requires genuine count–mark independence and Poisson exponential series, with integrability already established separately.
-- source:
--   Source-exact real Laplace portion of filtered-law core; use public Poisson jump-count law 5d293a54 and count-and-mark PGF machinery.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_compoundPoisson_laplace_identity
    (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
    [IsProbabilityMeasure P]
    (τ Y : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ)
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y (1 : ℝ≥0)
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) P) (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ *
      LevyFoundations.compoundPoisson (1 : ℝ) τ Y (t : ℝ) ω) ∂P) =
      Real.exp ((t : ℝ) *
        laplaceExponent
          ((1 : ℝ) + (∫ y in Ioo (-1 : ℝ) 0,
            y ∂((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0))))
          0 ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) θ) := by sorry
