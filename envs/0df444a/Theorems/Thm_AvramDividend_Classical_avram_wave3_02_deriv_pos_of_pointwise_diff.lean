-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
-- name    : AvramDividend.Classical.avram_wave3_02_deriv_pos_of_pointwise_diff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:46:15.339224+00:00
-- url     : https://prove2.me/theorems/40856b51-8cf8-482a-9786-8804fc973d69
-- title:
--   Strictly positive original q-scale derivative at each differentiability point
-- statement:
--   For the genuine Standing spectrally negative Levy process with q>0 and its q-scale W, the derivative is strictly positive at any positive point a where W is differentiable. Source-specific Esscher normalised monotonicity gives phi>0, W(a)>0 and phi W(a)≤W'(a), hence W'(a)>0. This removes all global C1 requirements from the positivity stage and isolates pointwise differentiability as the sole remaining analytic obligation.
-- source:
--   Original Levy Esscher scale monotonicity; Proved scaleFunction_tilted_positive_monotone and Proved normalized_derivative_lower_bound; Avram Palmowski Pistorius 2007.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_deriv_pos_of_pointwise_diff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hdiff : DifferentiableAt ℝ W a) :
    0 < deriv W a := by sorry
