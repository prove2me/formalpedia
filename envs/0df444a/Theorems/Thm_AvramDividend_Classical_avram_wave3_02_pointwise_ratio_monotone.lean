-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_pointwise_ratio_monotone
-- name    : AvramDividend.Classical.avram_wave3_02_pointwise_ratio_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:20:52.143671+00:00
-- url     : https://prove2.me/theorems/8adfc8c6-a397-4c36-ac9a-5fb8729d209c
-- title:
--   Genuine scale-function dividend quotient is monotone between differentiability points
-- statement:
--   For the genuine Standing spectrally negative Lévy model at positive discount, if positive barriers a≤b are each points of differentiability of the q-scale function W, the exact reflected Stieltjes dividend quotient W(a)/W'(a) does not exceed W(b)/W'(b), expressed in ENNReal. This uses two Proved source-level results: the true pointwise barrierSupValue identity and its pathwise-derived monotonicity in the barrier. It does not assume global C1, differentiability between the endpoints, or a stochastic surrogate.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 and monotonicity of (3.15), source-level reflected Stieltjes reward.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_pointwise_ratio_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b)
    (hda : DifferentiableAt ℝ W a)
    (hdb : DifferentiableAt ℝ W b) :
    ENNReal.ofReal (W a / deriv W a) ≤
      ENNReal.ofReal (W b / deriv W b) := by sorry
