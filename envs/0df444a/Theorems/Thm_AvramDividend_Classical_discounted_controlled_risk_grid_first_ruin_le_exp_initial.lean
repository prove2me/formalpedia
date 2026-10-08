-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_controlled_risk_grid_first_ruin_le_exp_initial
-- name    : AvramDividend.Classical.discounted_controlled_risk_grid_first_ruin_le_exp_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:43:15.190254+00:00
-- url     : https://prove2.me/theorems/b39f1e33-df86-4c13-9e4c-5ccf2e1c9471
-- title:
--   Controlled-risk discounted exponential at sampled ruin is bounded by the initial exponential reserve
-- statement:
--   At the first negative reserve sampled on a finite grid, the q-discounted exponential of the controlled Avram risk process has expectation at most exp(θx) for any dividend strategy, θ≥0 and q≥ψθ. This strengthens the earlier stopped-first-ruin inequality by evaluating the initial expectation using the exact pointwise starting conditions X0=0 and D0=0 and the probability mass of P.
-- source:
--   discounted_controlled_risk_grid_first_ruin_stopped_bound, SpectrallyNegativeLevy.X_zero, IsDividendStrategy D0=0, X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.discounted_controlled_risk_grid_first_ruin_le_exp_initial
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
      Real.exp (θ * x) := by sorry
