-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_disjoint_negative_bands_chronological_discounted_merge
-- name    : AvramDividend.Classical.avram_wave5_03_actual_disjoint_negative_bands_chronological_discounted_merge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:30:58.396207+00:00
-- url     : https://prove2.me/theorems/385506c9-3302-4f8e-a877-0df8ff1f3a76
-- title:
--   Actual two disjoint original negative Lévy jump bands merge without duplicated chronological dividends
-- statement:
--   For the original source X, controlled D and its ruin clock, two disjoint sets of strictly negative Levy jump sizes produce disjoint finite actual source event sets. The full discounted nonlinear post-source change, with positive pre-ruin right-dividend cash and ruin-inclusive source jump, and its original generator kernel term are each exactly additive across the band union, and the fully merged chronological jump-plus-cash sum obeys the generator-kernel bound. Directly imports the Proved canonical-hjump finite-band source estimate, no compensator assumptions, hC>0 or artificial process; supplies genuine chronological finite-band stitching for BV and UBV Ito–Meyer construction.
-- source:
--   Original SpectrallyNegativeLevy X and IsDividendStrategy D, accepted source helper 7e5af125, BV ef7e6c20, corrected UBV 429e17ca. Source jump-mark disjointness ensures exact no-double-count chronological merges.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_disjoint_negative_bands_chronological_discounted_merge
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
    (B₁ B₂ : Set ℝ)
    (hB₁ : B₁ ⊆ Iio (0 : ℝ)) (hB₂ : B₂ ⊆ Iio (0 : ℝ))
    (hBdisj : Disjoint B₁ B₂)
    (S₁ S₂ : Finset ℝ≥0)
    (hS₁ : ∀ r : ℝ≥0, r ∈ S₁ ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B₁)
    (hS₂ : ∀ r : ℝ≥0, r ∈ S₂ ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B₂) :
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
    let A : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        if Y r ∈ Icc (u + ζ) v then
          Real.exp (-(q * (r : ℝ))) *
            ((w (W r) - w (Function.leftLim
              (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r)
        else 0
      else 0
    let K : ℝ≥0 → ℝ := fun r =>
      if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
        if Y r ∈ Icc (u + ζ) v then
          Real.exp (-(q * (r : ℝ))) *
            ((if -1 < J r then J r * deriv w (Y r) else 0) +
              SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r))
        else 0
      else 0
    (∑ r ∈ S₁ ∪ S₂, A r) =
        (∑ r ∈ S₁, A r) + (∑ r ∈ S₂, A r) ∧
    (∑ r ∈ S₁ ∪ S₂, K r) =
        (∑ r ∈ S₁, K r) + (∑ r ∈ S₂, K r) ∧
    (∑ r ∈ S₁ ∪ S₂, A r) ≤
        (∑ r ∈ S₁ ∪ S₂, K r) := by sorry
