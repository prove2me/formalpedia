-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger127_original_zero_clock_full_correction
-- name    : AvramDividend.Classical.avram_gledger127_original_zero_clock_full_correction
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:18:23.09305+00:00
-- url     : https://prove2.me/theorems/8c4883c1-8b51-474f-b20e-862ee55828ff
-- title:
--   Full original zero stopped clock dividend contact correction
-- statement:
--   The complete original zero-stop dividend correction including strict discounted cash and the open terminal strip has nonpositive positive part, for any finite clipped grid. It follows from exact original finite-mesh contact telescoping and emptiness of pre-zero and final-zero payment domains.
-- source:
--   Original contact mesh exact equality gledger126 and original zero-clock strict/final cash vanish gledger125, both with identical original source X and dividend process D. This is the entire zero-clock branch of gledger81 without any positive-clock assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger127_original_zero_clock_full_correction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (ω : Ω) (q : ℝ) (Δ : ℝ≥0)
    (n N : ℕ) :
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) 0
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i => x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let F : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    let T : ℝ := (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
      Ioo (-(Δ : ℝ)) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
    max ((w (x - rightLimit D 0 ω) - w x) +
      (∑ i ∈ Finset.range N, E (v (i + 1)) *
        ((w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) +
         (w (Y (i + 1)) - w (riskProcess X x D (v (i + 1)) ω)))) +
      E 0 * (w (riskProcess X x D 0 ω) -
        w (x + X.X 0 ω - rightLimit D 0 ω)) + F) 0 ≤
      q * (Δ : ℝ) * Real.exp (q * (n : ℝ)) * F + T := by sorry
