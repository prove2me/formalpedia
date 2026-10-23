-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_esscher_positive_indicator_continuous
-- name    : AvramDividend.Classical.gaussian_esscher_positive_indicator_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T16:45:57.612308+00:00
-- url     : https://prove2.me/theorems/aa9f7441-42d0-47b5-96da-ac3e19a9e0e1
-- title:
--   Gaussian Esscher tilted scale's positive-halfline indicator is globally continuous
-- statement:
--   For a spectrally negative Lévy process with positive Gaussian coefficient and any q-scale function W, the positive-axis Esscher representative V agrees with exp(-φx)W(x) for x>0. W vanishes at zero by the proved Gaussian origin theorem, vanishes for x<0 by the scale-function support axiom, and is globally continuous by a proved continuity theorem. Thus the positive-half-line indicator of V equals the globally continuous function exp(-φx)W(x) at every real x, regardless of V outside x>0. This supports localised causal-convolution continuity.
-- source:
--   Proved scaleFunction_zero_origin_gaussian_without_standing, scaleFunction_continuous_of_zero_origin, IsScaleFunction support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuous_of_zero_origin
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.gaussian_esscher_positive_indicator_continuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (φ : ℝ) (V : ℝ → ℝ)
    (hV : ∀ x : ℝ, 0 < x →
      V x = Real.exp (-(φ * x)) * W x) :
    Continuous ((Ioi (0 : ℝ)).indicator V) := by sorry
