-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_actual_finite_negative_band_postsource_dividend_jump_balance
-- name    : AvramDividend.Classical.avram_wave5_03_actual_finite_negative_band_postsource_dividend_jump_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:41:25.981543+00:00
-- url     : https://prove2.me/theorems/2a80bc3f-1cc5-4c02-a30b-20ca765061b5
-- title:
--   Original finite-band source Lévy jump sum with chronological dividend after source jump and positive-ruin exclusion
-- statement:
--   On any finite collection that enumerates actual negative source Lévy jumps in a prescribed mark band between two real times, the genuine original controlled reserve value change plus admissible post-source right dividends, stopped at ruin inclusively for source marks but strictly for dividends, is bounded above by the finite generator Taylor and truncated-linear jump sums of the same original X. Actual cap, BV C1/UBV C2 local smoothness and gradient only; no source compensation, copied process, or boundary positivity is assumed. Uses canonical 03B Proved finite source band balance and canonical 03 right-atom control.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), jump part of (5.13); canonical Proved 03B finite band 715ac87b and Chat03 right atom 2cd50555; applicable to BV ef7e6c20 and UBV 429e17ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_stopped_riskProcess_finite_band_ito_jump_balance
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_separate_gradient_right_atom_control

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_actual_finite_negative_band_postsource_dividend_jump_balance
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (u v ζ : ℝ)
    (s t : ℝ≥0) (ω : Ω)
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
        (w (W r) - w (Function.leftLim
          (fun a : ℝ≥0 => riskProcess X x D a ω) r)) + cash r
       else 0) else 0) ≤
    (∑ r ∈ S, if (r : ℝ≥0∞) ≤ ruinTime X x D ω then
      (if -1 < J r then
        J r * (if Y r ∈ Icc (u + ζ) v then deriv w (Y r) else 0)
       else 0) +
      (if Y r ∈ Icc (u + ζ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y r) (J r)
       else 0)
      else 0) := by sorry
