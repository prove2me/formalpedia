-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_original_killed_HJB_scale_comparison
-- name    : AvramDividend.Classical.avram_p4_f6_original_killed_HJB_scale_comparison
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T09:14:30.094899+00:00
-- url     : https://prove2.me/theorems/fe2d23f9-a88a-4733-91a8-6ce8d935cbd7
-- title:
--   Killed original Lévy HJB supersolution is dominated by the positive q-scale ratio
-- statement:
--   For the original spectrally negative Lévy process with positive Gaussian volatility and negative jumps, an HJB supersolution w vanishing at negative reserves, with derivative floor, is dominated above level one by the corresponding q-scale function: w(b)W(1)≤w(1)W(b), for b≥1 and any q-scale W with W(1)>0. Proof requires a genuine killed two-sided-upcrossing optional stopping argument from strictly positive initial reserve, retaining the down-exit boundary and the original generator. It is the hard stochastic comparison component of analytic growth target 51922c24.
-- source:
--   Source-faithful nontrivial HJB stopping/localisation reduction of 51922c24, independent of the already published gaussian q-scale exponential upper bound b114eb46 and deterministic scale domination bridge 9e0c1855. Care needed with time-zero local time, down ruin and integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_original_killed_HJB_scale_comparison
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (hWone : 0 < W 1) :
    ∀ b : ℝ, 1 ≤ b → w b * W 1 ≤ w 1 * W b := by sorry
