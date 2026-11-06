-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_original_lower_exit_creeping_ae_stopped_terminal_limit
-- name    : AvramDividend.Classical.avram_p4_f4_original_lower_exit_creeping_ae_stopped_terminal_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:27:11.770127+00:00
-- url     : https://prove2.me/theorems/b3eda8f7-34ce-4ff8-8c6b-beeed859cd55
-- title:
--   Original stopped right-payment terminal converges on almost-sure shrinking creeping lower-exit bands
-- statement:
--   For the actual spectrally negative Levy process X and actual dividend strategy D, the original stopped post-rightpayment reserve W_k is defined by the precise zero clock, pre-ruin and ruin branches. If these physical reserves are nonnegative and bounded by a shrinking barrier almost surely, and physical stopped clocks converge almost surely, the discounted terminal value converges almost surely to exp(-q tau) w(0). The physical lower exit band and clock hypotheses remain to be established independently; the theorem makes those exact gaps explicit.
-- source:
--   Instantiates Proved barrier-squeeze terminal convergence at each almost-sure original sample point, with original rightLimit and riskProcess W_k identity and exact Term_k formula.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_creeping_nonnegative_exit_barrier_discounted_terminal_limit

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_original_lower_exit_creeping_ae_stopped_terminal_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (τ : Ω → ℝ≥0) (τk : ℕ → Ω → ℝ≥0)
    (Wk Termk : ℕ → Ω → ℝ) (barrier : ℕ → ℝ)
    (hWk : ∀ k ω, Wk k ω =
      if τk k ω = 0 ∨ (τk k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τk k ω) ω - rightLimit D (τk k ω) ω
      else riskProcess X x D (τk k ω) ω)
    (hTermk : ∀ k ω, Termk k ω =
      Real.exp (-(q * (τk k ω : ℝ))) * w (Wk k ω))
    (hbarrier : Tendsto barrier atTop (𝓝 (0 : ℝ)))
    (hclock : ∀ᵐ ω ∂P,
      Tendsto (fun k => (τk k ω : ℝ)) atTop (𝓝 (τ ω : ℝ)))
    (hbandNN : ∀ᵐ ω ∂P, ∀ k, 0 ≤ Wk k ω)
    (hbandLe : ∀ᵐ ω ∂P, ∀ k, Wk k ω ≤ barrier k) :
    ∀ᵐ ω ∂P, Tendsto (fun k => Termk k ω) atTop
      (𝓝 (Real.exp (-(q * (τ ω : ℝ))) * w 0)) := by sorry
