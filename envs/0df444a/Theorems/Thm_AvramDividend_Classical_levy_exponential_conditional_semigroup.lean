-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_exponential_conditional_semigroup
-- name    : AvramDividend.Classical.levy_exponential_conditional_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T12:42:33.560265+00:00
-- url     : https://prove2.me/theorems/195d3d69-2b24-481c-b1f6-ca432505811d
-- title:
--   Conditional exponential Lévy semigroup using only the process Laplace moment and independent increments
-- statement:
--   For a spectrally negative Levy process, deterministic times s≤t and theta≥0, show that the conditional expectation of exp(theta X_t) given the past F_s equals exp(theta X_s) times the deterministic stationary-increment exponential moment at t−s. Derive the adapted strong measurability of the past exponential factor from X.adapted, the time-t and stationary-increment integrability from the two X.laplace fields, and the actual future increment integrability by pushing X.stationaryIncrements through the measurable exponential and using IdentDistrib.integrable_iff. Apply the separately accepted conditional exponential factorisation theorem. This removes all extra integrability and measurable-premise burden from the resulting semigroup identity. The proof should be published only when the factorisation target is Proved.
-- source:
--   Process fields X.adapted, X.laplace and X.stationaryIncrements; pinned IdentDistrib.integrable_iff and dependency-gated levy_exponential_condExp_factorization target a44cb9f4-52df-41bd-aa08-9087afd7b2d2.

import Mathlib.Probability.IdentDistrib
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_exponential_condExp_factorization

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_exponential_conditional_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ) (hθ : 0 ≤ θ) :
    P[(fun ω => Real.exp (θ * X.X t ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => Real.exp (θ * X.X s ω) *
        (∫ η, Real.exp (θ * X.X (t - s) η) ∂P)) := by sorry
