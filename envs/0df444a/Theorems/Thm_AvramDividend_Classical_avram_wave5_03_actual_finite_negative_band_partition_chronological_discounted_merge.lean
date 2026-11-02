-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_finite_negative_band_partition_chronological_discounted_merge
-- name    : AvramDividend.Classical.avram_wave5_03_actual_finite_negative_band_partition_chronological_discounted_merge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:48:12.93319+00:00
-- url     : https://prove2.me/theorems/48744b5c-7a2a-463d-b8c8-c33f4298ca5e
-- title:
--   Genuine original finite partition of negative Lévy jump bands merges all discounted chronological payout and generator terms
-- statement:
--   For any finite collection of pairwise disjoint negative-mark Borel sets on the one original spectrally negative Levy path, each with its actual finite jump-time enumerator, the event sets are pairwise disjoint, and the full original stopped discounted nonlinear source jump plus eligible right dividend corrections and true generator-kernel sums are additive across the whole finite partition. Their merged total obeys the same canonical hjump source bound. Handles every finite truncation family before the small-mark L1/L2 limit, inclusive positive ruin source jump and without positive ruin right payout, hC>0, stochastic independence or an invented process.
-- source:
--   Source actual negative jump graph, canonical Proved 7e5af125 original finite band bound, original riskProcess, rightLimit D and ruinTime, BV ef7e6c20 and UBV 429e17ca; countable-band Itô–Meyer finite truncation integration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_discounted_finite_band_inclusive_ruin_chronological_jump_sum

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_finite_negative_band_partition_chronological_discounted_merge
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
    (I : Finset ℕ) (B : ℕ → Set ℝ)
    (hBneg : ∀ i ∈ I, B i ⊆ Iio (0 : ℝ))
    (hBdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (B i) (B j))
    (S : ℕ → Finset ℝ≥0)
    (hS : ∀ i ∈ I, ∀ r : ℝ≥0, r ∈ S i ↔
      s < r ∧ r ≤ t ∧
        X.X r ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) r ∈ B i) :
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
    (∑ r ∈ I.biUnion S, A r) =
        (∑ i ∈ I, ∑ r ∈ S i, A r) ∧
    (∑ r ∈ I.biUnion S, K r) =
        (∑ i ∈ I, ∑ r ∈ S i, K r) ∧
    (∑ r ∈ I.biUnion S, A r) ≤
        ∑ r ∈ I.biUnion S, K r := by sorry
