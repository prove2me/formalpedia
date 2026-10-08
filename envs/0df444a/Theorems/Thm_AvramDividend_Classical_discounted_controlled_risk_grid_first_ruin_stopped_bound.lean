-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_controlled_risk_grid_first_ruin_stopped_bound
-- name    : AvramDividend.Classical.discounted_controlled_risk_grid_first_ruin_stopped_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:37:43.459018+00:00
-- url     : https://prove2.me/theorems/96df2c00-b0bf-4bcf-8ac8-232ce2533ad9
-- title:
--   Controlled risk exponential satisfies bounded grid-first-ruin optional stopping
-- statement:
--   For any admissible dividend trajectory in the mission model, the q-discounted exponential of the actual controlled reserve U=x+X−D, stopped at the first observed negative reserve in [0,N], has expected value bounded by its expected initial exponential. The key input is the already-proved riskProcess adaptedness and a controlled exponential supermartingale, restricted to the exact grid filtration, plus accepted bounded optional stopping. This is a meaningful special stochastic verification bound but not the full continuous-time dividend payout theorem.
-- source:
--   AvramDividend.Classical.riskProcess_adapted; discounted_controlled_risk_exponential_supermartingale and accepted sampled-supermartingale and hittingBtwn optional-stopping results.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_controlled_risk_grid_first_ruin_stopped_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {𝓖 : Filtration ℕ mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h𝓖 : ∀ n : ℕ, 𝓖 n = 𝓕 (n : ℝ≥0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (N : ℕ) :
    (∫ ω, stoppedValue
      (fun n : ℕ => fun ω =>
        Real.exp (θ * riskProcess X x D (n : ℝ≥0) ω -
          ((n : ℝ≥0) : ℝ) * q))
      (fun ω => ((hittingBtwn
        (fun n : ℕ => fun ω => riskProcess X x D (n : ℝ≥0) ω)
        (Iio (0 : ℝ)) 0 N ω : ℕ) : WithTop ℕ)) ω ∂P) ≤
      ∫ ω, Real.exp (θ * riskProcess X x D 0 ω) ∂P := by sorry
