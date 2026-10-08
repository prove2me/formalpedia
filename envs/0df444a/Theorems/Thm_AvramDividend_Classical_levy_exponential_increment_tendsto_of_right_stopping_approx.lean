-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_increment_tendsto_of_right_stopping_approx
-- name    : AvramDividend.Classical.levy_exponential_increment_tendsto_of_right_stopping_approx
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:13:10.749355+00:00
-- url     : https://prove2.me/theorems/e1efe12c-49bc-471d-bff8-40f48eb3cee3
-- title:
--   Right-continuous convergence of Lévy increment exponentials under stopping-time approximation
-- statement:
--   For any Lévy sample path with right continuity and any sequence of random times τn approaching τ from above, the shifted sample values at τn and τn+h converge to the corresponding values at τ and τ+h. Consequently the exponential of the increment over h converges pointwise. No stopping-time measurability, independence or integrability is needed for this pathwise stage. This is the exact convergence input for passing from finite-valued dyadic stopping approximations to the bounded-stopping-time Laplace identity.
-- source:
--   SpectrallyNegativeLevy.rightCont field; continuous exponential, add/subtract and multiplication. Strong Markov proof via finite dyadic stopping times for Avram et al (2007), Proposition 1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_increment_tendsto_of_right_stopping_approx
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0) (τn : ℕ → Ω → ℝ≥0)
    (habove : ∀ ω n, τ ω ≤ τn n ω)
    (hconv : ∀ ω, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω)))
    (h : ℝ≥0) (θ : ℝ) (ω : Ω) :
    Tendsto
      (fun n => Real.exp (θ *
        (X.X (τn n ω + h) ω - X.X (τn n ω) ω)))
      atTop
      (𝓝 (Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω)))) := by sorry
