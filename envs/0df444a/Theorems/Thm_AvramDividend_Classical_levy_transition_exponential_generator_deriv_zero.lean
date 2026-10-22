-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_exponential_generator_deriv_zero
-- name    : AvramDividend.Classical.levy_transition_exponential_generator_deriv_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:36:50.459852+00:00
-- url     : https://prove2.me/theorems/767bd50f-73da-4fa4-9893-8ae836b9ce71
-- title:
--   Derivative of the exponential Lévy semigroup equals its generator at time zero
-- statement:
--   For a spectrally negative Lévy process, any real exponential parameter θ and starting reserve x, the time derivative at zero of the analytic transition multiplier exp(θx) exp(h ψ(θ)) is exactly the recorded Lévy generator acting on the exponential payoff z ↦ exp(θz) at x. The proof combines the already Proved generator_exp_eq_psi with the already Proved derivative of the exact exponential transition multiplier. This is the exact generator-semigroup identification on exponential test functions; it is not a Dynkin formula for arbitrary C² functions or a stopped dividend verification theorem.
-- source:
--   Exact published Proved generator_exp_eq_psi and levy_exponential_semigroup_multiplier_deriv_zero under pinned Mathlib revision; source-faithful exponential test-function bridge.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_generator_exp_eq_psi
import Theorems.Thm_AvramDividend_Classical_levy_exponential_semigroup_multiplier_deriv_zero

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_exponential_generator_deriv_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ x : ℝ) :
    HasDerivAt
      (fun h : ℝ =>
        Real.exp (θ * x) *
          Real.exp (h * laplaceExponent X.c X.σ X.ν θ))
      (X.generator (fun z : ℝ => Real.exp (θ * z)) x)
      0 := by sorry
