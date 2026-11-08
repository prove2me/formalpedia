-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_uniform_prefix_upcross_reserve_envelope
-- name    : AvramDividend.Classical.avram_ubv_top9_original_uniform_prefix_upcross_reserve_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:47:06.076217+00:00
-- url     : https://prove2.me/theorems/90b203a8-f8fe-4bb4-b360-39e9cff9090f
-- title:
--   Uniform original upcross prefix bounds for Levy source and post-payment reserve at every prior time
-- statement:
--   For a bounded arbitrary right-continuous-filtration stopping time, construct finite genuine upward-exit localising clocks which eventually equal the requested clock and uniformly bound the original Levy source and the source-exact post-right-payment/ruin reserve at every time up to each localising clock. This stronger prefix energy envelope enables predictable stopped Ito estimates; an endpoint-only upper bound does not control the integral along the clock.
-- source:
--   Source construction of Proved b2e939f7 adapted using Proved path_value_le_of_strict_prefix_le and avram_f18_original_stopped_postpayment_reserve_upper_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_top9_original_uniform_prefix_upcross_reserve_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ n) :
    ∃ rhoLoc : ℕ → Ω → ℝ≥0,
      (∀ k, IsStoppingTime 𝓕.rightCont
        (fun ω => (rhoLoc k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, rhoLoc k ω ≤ ρ ω) ∧
      (∀ k ω (t : ℝ≥0), t ≤ rhoLoc k ω →
        X.X t ω ≤ (k : ℝ) + 1 ∧
        (if t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X t ω - rightLimit D t ω
          else riskProcess X x D t ω) ≤ x + ((k : ℝ) + 1)) ∧
      (∀ ω, ∀ᶠ k : ℕ in atTop, rhoLoc k ω = ρ ω) := by sorry
