-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
-- name    : AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:15:46.133202+00:00
-- url     : https://prove2.me/theorems/a849869c-3e67-4861-9bcf-5727858c3bc0
-- title:
--   Original BV strict-survival signed terminal is L1 and has the same expected value as the positive terminal
-- statement:
--   For positive finite horizon and original capped BV dividend strategies, the genuine signed stopped candidate terminal is integrable, and its real expectation equals that of the positive-part terminal appearing in W8-04 source statement. Follows from pointwise strict-survival nonnegative value via the cap gradient secant and full original finite-horizon L1 theorem. Bridges exact Itô identity to source reward without extra assumptions.
-- source:
--   Original source Proposition 4(i), stopped inequality (5.13); exact terminal integral identity for original process and rightLimit D at T.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_04_original_BV_positive_horizon_signed_terminal_integrable_mean_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T) :
    let S : ℝ≥0 := ⟨T,hT⟩
    let Signed : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)
      else 0
    let Positive : Ω → ℝ := fun ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω))
      else 0
    Integrable Signed P ∧
      (∫ ω, Signed ω ∂P) = (∫ ω, Positive ω ∂P) := by sorry
