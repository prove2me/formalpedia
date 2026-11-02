-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum
-- name    : AvramDividend.Classical.avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:58:57.673655+00:00
-- url     : https://prove2.me/theorems/7e5af125-b3b0-41c1-8c69-0450b766922f
-- title:
--   Canonical BV/UBV directly compatible original discounted finite-band negative source jumps plus right payouts, inclusive positive ruin
-- statement:
--   Assuming only the exact source dividend-strategy and original-path right-lump secant hjump ALREADY PRESENT in both canonical BV and corrected UBV targets, sum the full discounted chronological source negative marks and eligible right payouts at finitely enumerated original jump times. Source ruin mark is included; right cash at positive ruin is excluded. Result bounded by the true original source generator kernel sum plus small-jump linear sum. No hC>0 or extra positivity/smoothness assumptions, so type-compatible also with corrected UBV C=0; no automatic compensation or martingale is claimed.
-- source:
--   Avram Palmowski Pistorius (2007) Proposition4(i), actual finite source band; uses Proved prerequisite canonical-hjump inclusive-ruin single-jump theorem; direct BV ef7e6c20 and UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_canonical_hjump_inclusive_ruin_source_discounted_jump_bound

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (q : ℝ)
    (u v ζ : ℝ) (s t : ℝ≥0) (ω : Ω)
    (B : Set ℝ) (hBneg : B ⊆ Iio (0 : ℝ))
    (S : Finset ℝ≥0)
    (hS : ∀ r : ℝ≥0, r ∈ S ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B) :
    let Y : ℝ≥0 → ℝ := fun r => Function.leftLim
      (fun a : ℝ≥0 => x + X.X a ω - rightLimit D a ω) r
    let J : ℝ≥0 → ℝ := fun r =>
      X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r
    let W : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X r ω - rightLimit D r ω
      else riskProcess X x D r ω
    let cash : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) < ruinTime X x D ω then
        rightLimit D r ω - D r ω else 0
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y r ∈ Icc (u + ζ) v then
        Real.exp (-(q * (r : ℝ))) *
        ((w (W r) - w (Function.leftLim
          (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
       else 0) else 0) ≤
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if Y r ∈ Icc (u + ζ) v then
        Real.exp (-(q * (r : ℝ))) *
          ((if -1 < J r then J r * deriv w (Y r) else 0) +
           SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r))
       else 0) else 0) := by sorry
