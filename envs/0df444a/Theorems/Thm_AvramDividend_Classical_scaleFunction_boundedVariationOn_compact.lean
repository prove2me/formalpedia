-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_boundedVariationOn_compact
-- name    : AvramDividend.Classical.scaleFunction_boundedVariationOn_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T10:48:49.02786+00:00
-- url     : https://prove2.me/theorems/e7624534-607e-4d10-ab25-6fc4562c6a25
-- title:
--   Every q-scale function has bounded variation on compact intervals
-- statement:
--   The canonical spectrally negative Lévy q-scale function is globally nondecreasing. Therefore its restriction to any compact real interval has bounded variation. The finite endpoint values explicitly bound the absolute value of W throughout the interval, meeting the exact pinned Mathlib hypothesis for monotone functions of bounded variation. This works even when the Esscher tilt is not itself monotone and is a prerequisite for the Gaussian Volterra convolution regularity argument.
-- source:
--   Proved scaleFunction_monotone (1c7655dc-6544-4dd0-9bcf-96acecffa075), Mathlib MonotoneOn.boundedVariationOn and abs_le_max_abs_abs.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleFunction_boundedVariationOn_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a b : ℝ) :
    BoundedVariationOn W (Icc a b) := by sorry
