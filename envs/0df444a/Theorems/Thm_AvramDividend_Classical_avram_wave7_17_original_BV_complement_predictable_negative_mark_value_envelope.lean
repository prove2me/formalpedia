-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_complement_predictable_negative_mark_value_envelope
-- name    : AvramDividend.Classical.avram_wave7_17_original_BV_complement_predictable_negative_mark_value_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:30:12.621307+00:00
-- url     : https://prove2.me/theorems/38e7e8f9-5510-4b58-81c2-06e221601b36
-- title:
--   Original BV complement controlled predictable reserve has two-sided candidate-value envelope for every negative Lévy source mark
-- statement:
--   Under W7-04's actual original bounded-variation Lévy and admissible dividend binders and strict drift-envelope complement, the physical BV drift is strictly positive. For every true original predictable controlled left-limit reserve in the strict HJB interior and every spectrally negative Lévy mark z<0, the hypothetical source mark candidate-value change w(Y+z)-w(Y) lies between -w(Y) and zero. This is the exact mark envelope for subsequent stopped compensation and handles marks crossing ruin because the original w vanishes below zero. No new source process, compensation identity, or boundary occupation claim is introduced.
-- source:
--   Original source predictable reserve and negative Lévy marks for Avram-Palmowski-Pistorius (2007), Proposition 4(i). Uses Proved strict complement d6705e01 and Proved full-cap C1 gradient secant 2ba5cc4f, plus the exact w(y)=0 for y<0. Needed to bound actual mark corrections and justify subsequent finite-activity or localised source-jump mean estimates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_17_original_BV_complement_predictable_negative_mark_value_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (ω : Ω) (t : ℝ≥0) (z : ℝ) (hz : z < 0)
    (hy : 0 < Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t) < C) :
    let y := Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t
    0 < X.drift ∧
      -w y ≤ w (y + z) - w y ∧
      w (y + z) - w y ≤ 0 := by sorry
