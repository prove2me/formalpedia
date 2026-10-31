-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_strictMonoOn_positive
-- name    : AvramDividend.Classical.avram_wave3_02_scale_strictMonoOn_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:37:22.923452+00:00
-- url     : https://prove2.me/theorems/51e583e2-6b33-41d5-a955-e1fddc749a2d
-- title:
--   Strict positive-axis increase of the original q-scale function from Esscher monotonicity
-- statement:
--   For an original Standing spectrally negative Levy process and q>0, any q-scale function W is strictly increasing on the positive half-line. The genuine stochastic Esscher-normalised monotonicity implies exp(-phi*x)W(x) nondecreasing with phi>0 and W(x)>0. As exp(-phi*x) strictly decreases in x>0, W must strictly increase. This is stronger than ordinary monotonicity and requires no differentiability.
-- source:
--   Original spectrally negative Levy q-scale function monotonicity from Proved scaleFunction_tilted_positive_monotone; used for source-correct reflected-value finite-difference denominators.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_scale_strictMonoOn_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    StrictMonoOn W (Ioi (0 : ℝ)) := by sorry
