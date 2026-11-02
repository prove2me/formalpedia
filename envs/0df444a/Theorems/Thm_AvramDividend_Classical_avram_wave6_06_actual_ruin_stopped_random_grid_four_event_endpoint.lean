-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint
-- name    : AvramDividend.Classical.avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:19:13.206376+00:00
-- url     : https://prove2.me/theorems/e92ede42-dd1e-40b4-b913-c00138f6c8aa
-- title:
--   Original Lévy ruin-stopped random-grid four-event discounted chain with exact positive-ruin book terminal correction
-- statement:
--   For the same original spectrally negative Lévy path, dividend strategy, and sample of a random stop at or before original ruin, clip any deterministic increasing clock to that realised stop. The discounted controlled four-event telescoping identity then holds exactly, including the time-zero right-dividend atom. At a strictly positive ruin endpoint the left side is the pre-right-payment book reserve rather than the post-right-payment state; its explicit correction is the terminal book/postpayment difference. At time zero the postpayment reserve is used and no positive-ruin correction appears. This pathwise identity is the finite-grid entry point for the controlled Ito–Meyer limit, but claims neither the jump compensator nor the continuum martingale identity.
-- source:
--   Avram Prop.4(i), Eq.(5.13), source-controlled original ruin terminal convention. Imports Proved 6e9ccb50 finite-grid four-event identity. This is the first exact random-stop alignment to the eventual continuum stochastic chain, not its replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_original_controlled_four_term_discounted_finite_grid_chain
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave6_06_actual_ruin_stopped_random_grid_four_event_endpoint
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω)
    (τ : Ω → ℝ≥0)
    (hτruin : (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (hzero : u 0 = 0) (n : ℕ) (hcover : τ ω ≤ u n) :
    let v : ℕ → ℝ≥0 := fun i => min (u i) (τ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let pre : Prop := τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
    let W : ℝ := if pre then Y (τ ω) else riskProcess X x D (τ ω) ω
    E (τ ω) * w W =
      w x + (w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range n,
        ((E (v (i + 1)) - E (v i)) * w (Y (v i)) +
          E (v (i + 1)) * (w (Z i) - w (Y (v i))) +
          E (v (i + 1)) *
            (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
          E (v (i + 1)) *
            (w (Y (v (i + 1))) -
              w (riskProcess X x D (v (i + 1)) ω)))) +
      (if pre then 0 else
        E (τ ω) *
          (w (riskProcess X x D (τ ω) ω) - w (Y (τ ω)))) := by sorry
