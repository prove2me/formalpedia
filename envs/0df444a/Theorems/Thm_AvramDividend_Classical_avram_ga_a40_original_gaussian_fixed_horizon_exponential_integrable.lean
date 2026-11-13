-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a40_original_gaussian_fixed_horizon_exponential_integrable
-- name    : AvramDividend.Classical.avram_ga_a40_original_gaussian_fixed_horizon_exponential_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:43:16.163515+00:00
-- url     : https://prove2.me/theorems/5632fbfe-4148-4de8-b169-bf6c4b7c1017
-- title:
--   Original Gaussian finite-horizon running-supremum exponential moment is finite
-- statement:
--   For the original spectrally negative Levy process with nonzero Gaussian coefficient, and any nonnegative exponential exponent beta, the exponential of beta times its running supremum has a finite positive integral over every finite nonnegative horizon. Use the actual probability law P from the process structure, a positive Laplace root above beta (a37), the finite exponential-clock supremum product moment (a39), the strictly positive exponential clock survival probability, and the Fubini fixed-horizon transfer (a38). This supplies the major integrability ingredient in the original terminal Gaussian positive L1 envelope d9c4650e.
-- source:
--   Original top-cap Gaussian terminal envelope d9c4650e; previously accepted a37, a36 and clock-source identities.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a37_gaussian_positive_rate_above_growth
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_expMeasure_strict_survival_positive
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a40_original_gaussian_fixed_horizon_exponential_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hSigma : 0 < X.σ)
    (n : ℝ≥0) (beta : ℝ) (hbeta : 0 ≤ beta) :
    (∫⁻ ω : Ω,
      ENNReal.ofReal (Real.exp (beta * runningSup X n ω))
        ∂ P) < ⊤ := by sorry
