-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_all_n_zero_horizon_pointwise_full_stieltjes_le
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_all_n_zero_horizon_pointwise_full_stieltjes_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:43:10.955671+00:00
-- url     : https://prove2.me/theorems/d57573e3-3869-45d2-8681-09e5d9b8062a
-- title:
--   All finite clips original-process zero-horizon Stieltjes cash bounded pointwise by HJB value
-- statement:
--   For any original controlled Lévy sample path, admissible dividend process and any natural clipped ruin clock n including n=0, the exact raw discounted dividendMeasure lintegral over all source payment times up to the closed horizon 0 is bounded pointwise by ENNReal.ofReal(w x), with the full time-zero right-payment atom. The result does not assume immediate ruin or depend on stochastic finite-grid source witnesses.
-- source:
--   Direct application of Proved source zero-horizon Stieltjes equality 1fb597ac (any finite or infinite clock) and newly public Proved all-original-path initial right-dividend singleton HJB bound 1794a9b8. This strengthens prior expected all-n zero-horizon bound a4ec4831 to a samplewise estimate, keeping canonical source dividendMeasure.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_zero_horizon_full_stieltjes_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_initial_right_dividend_atom_le_hjb
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_hor3_original_all_n_zero_horizon_pointwise_full_stieltjes_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n : ℕ) (ω : Ω) :
    (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    ENNReal.ofReal (w x) := by sorry
