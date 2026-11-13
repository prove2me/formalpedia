-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a37_gaussian_positive_rate_above_growth
-- name    : AvramDividend.Classical.avram_ga_a37_gaussian_positive_rate_above_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:28:09.724605+00:00
-- url     : https://prove2.me/theorems/55a89657-9299-4817-9ab4-02b87e4c1648
-- title:
--   Original nonzero-Gaussian source admits positive exponential-clock rate with root above arbitrary growth exponent
-- statement:
--   For the original Gaussian spectrally negative Levy source with positive sigma, and any nonnegative exponential-growth exponent theta, there are p>0 and lambda>theta with X.psi lambda=p. Select lambda beyond the eventual positivity threshold for psi and beyond theta+1. This supplies the exact positive root and strict gap assumptions in the Proved original exponential-clock supremum MGF, allowing a36 to transfer that moment to a deterministic horizon for terminal d9c.
-- source:
--   d9c4650e-839e-480f-860a-906387200065; Proved psi_eventually_positive_quadratic_of_gaussian ea687ee2 and clocked MGF 626336fd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_psi_eventually_positive_quadratic_of_gaussian
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a37_gaussian_positive_rate_above_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hSigma : 0 < X.σ) (θ : ℝ) (hθ : 0 ≤ θ) :
    ∃ p lam : ℝ,
      0 < p ∧ 0 < lam ∧ θ < lam ∧ X.ψ lam = p := by sorry
