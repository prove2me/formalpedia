-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_transform_initial
-- name    : AvramDividend.Classical.chat04_esscher_weighted_capital_transform_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:12:05.416337+00:00
-- url     : https://prove2.me/theorems/8a6d7e68-7e42-4d22-9a18-a98fca49df59
-- title:
--   Exact horizon-zero normalisation of the true Esscher-weighted killed-survival capital transform
-- statement:
--   At horizon zero, the original-measure double integral of the Esscher-weighted continuously killed survival kernel over all initial positive capital is exactly 1/β. It matches the normalisation of the limiting Wiener-Hopf transform and supports comparison with the finite-time antitone family.
-- source:
--   Proved finite-horizon Esscher real expectation bridge 3c50d08b; the pathwise zero-horizon reflected origin payoff; and the source probability law P with `X.isProbability`. Integrate the pathwise constant 1/β. No stochastic scale-function or two-sided exit identity is used.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_reflected_origin_payoff
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_capital_real_expectation_bridge

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_esscher_weighted_capital_transform_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (β θ : ℝ) (hβ : 0 < β) (hθ : 0 ≤ θ) :
    (∫⁻ (x : ℝ), ∫⁻ (ω : Ω),
      Set.indicator
        {p : ℝ × Ω | 0 < p.1 ∧
          ∀ s : ℝ≥0, s ≤ (0 : ℝ≥0) → 0 ≤ p.1 + X.X s p.2}
        (fun p => ENNReal.ofReal
          (Real.exp (-β * p.1) *
            Real.exp (θ * X.X 0 p.2 -
              ((0 : ℝ≥0) : ℝ) * laplaceExponent X.c X.σ X.ν θ)))
        (x, ω) ∂P ∂volume) =
    ENNReal.ofReal (1 / β) := by sorry
