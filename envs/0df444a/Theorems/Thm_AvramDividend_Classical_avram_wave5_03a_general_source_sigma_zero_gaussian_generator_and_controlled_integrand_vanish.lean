-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_general_source_sigma_zero_gaussian_generator_and_controlled_integrand_vanish
-- name    : AvramDividend.Classical.avram_wave5_03a_general_source_sigma_zero_gaussian_generator_and_controlled_integrand_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:34:05.45956+00:00
-- url     : https://prove2.me/theorems/411edd4a-28bb-440d-82a0-aba6df7dcaae
-- title:
--   General original jump Lévy source with sigma zero has no Gaussian generator or controlled stochastic coefficient
-- statement:
--   On any original SpectrallyNegativeLevy process, for arbitrary jump measure ν and any admissible full Stieltjes dividend control, if σ=0 then both the Gaussian generator coefficient σ²/2 times w'' at the true prepayment strict-left reserve and the discounted Gaussian stochastic coefficient exp(-qt) σ times its capped gradient vanish pointwise. No pure-Gaussian (ν=0) hypothesis is imposed on the general root case. This formalises that the Gaussian component is absent rather than adding an artificial Gaussian hypothesis; no stochastic integral or Ito chain rule is claimed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_general_source_sigma_zero_gaussian_generator_and_controlled_integrand_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hσ : X.σ = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (q : ℝ) (t : ℝ≥0) (ω : Ω) :
    let Y : ℝ := Function.leftLim
      (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t
    (X.σ ^ 2 / 2) * iteratedDeriv 2 w Y = 0 ∧
    Real.exp (-(q * (t : ℝ))) * X.σ *
      (if 0 < Y ∧ ENNReal.ofReal Y < C then deriv w Y else 0) = 0 := by
  sorry
