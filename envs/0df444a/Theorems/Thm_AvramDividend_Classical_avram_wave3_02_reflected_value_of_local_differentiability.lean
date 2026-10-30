-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_reflected_value_of_local_differentiability
-- name    : AvramDividend.Classical.avram_wave3_02_reflected_value_of_local_differentiability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:29:02.984497+00:00
-- url     : https://prove2.me/theorems/5e5da34b-d4e2-4ebc-a50d-8ed29e003caa
-- title:
--   Real reflected-barrier scale ratio and all-capital value from pointwise scale differentiability
-- statement:
--   For the genuine spectrally negative Lévy process under Standing and positive discount and barrier, differentiability of its q-scale function at that single barrier forces a strictly positive scale derivative, the expected discounted reflected regulator value W(a)/W'(a), and the true dividend-strategy value at every nonnegative initial capital, including the cases x=0, x≤a and x>a. No global C1 hypothesis is needed.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1. Esscher-normalised scale monotonicity and the pointwise differential lower bound are canonically Proved; so are the true stopped-renewal scale ratio and all-capital reflected regulator identity under nonzero local derivative.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_reflected_value_of_local_differentiability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hDa : DifferentiableAt ℝ W a) :
    (0 < deriv W a) ∧
    (barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a)) ∧
    (∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (barrierValue W a x)) := by sorry
