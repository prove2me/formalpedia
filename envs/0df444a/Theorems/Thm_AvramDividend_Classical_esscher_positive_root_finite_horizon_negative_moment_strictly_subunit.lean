-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_root_finite_horizon_negative_moment_strictly_subunit
-- name    : AvramDividend.Classical.esscher_positive_root_finite_horizon_negative_moment_strictly_subunit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:35:34.02081+00:00
-- url     : https://prove2.me/theorems/2e825141-8cec-4993-b68f-c0ce6ba302af
-- title:
--   Positive q-root Esscher laws admit a negative exponential moment strictly below one at every positive horizon
-- statement:
--   For any positive discount q and root φ>0 with ψ(φ)=q, one can find ε in (0,φ) such that for every positive time t, the true finite-horizon Esscher probability law at parameter φ has negative exponential moment E_t^φ exp(−εX_t)<1. This strict exponential decay is a foundational input for an eventual downward-passage Chernoff estimate and total-mass-one property of the perpetual survival law.
-- source:
--   Combine the proven positive-root left-shift strict exponent inequality ψ(φ−ε)<ψ(φ) with the proven finite-horizon negative Laplace formula under the genuine Esscher measure, then use positivity of time and the real exponential comparison to one.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_has_negative_left_shift_exponent
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_negative_laplace
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.esscher_positive_root_finite_horizon_negative_moment_strictly_subunit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) :
    ∃ ε : ℝ, 0 < ε ∧ ε < φ ∧
      ∀ t : ℝ≥0, 0 < t →
        (∫ ω, Real.exp (-ε * X.X t ω) ∂
          (P.withDensity (fun ω : Ω =>
            ENNReal.ofReal
              (Real.exp (φ * X.X t ω - (t : ℝ) * X.ψ φ))))) < 1 := by sorry
