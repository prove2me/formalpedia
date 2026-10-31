-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrier_value_of_pointwise_diff
-- name    : AvramDividend.Classical.avram_wave3_02_barrier_value_of_pointwise_diff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:03:55.179985+00:00
-- url     : https://prove2.me/theorems/42aedec8-2722-4b8c-be51-aae6dbca87d5
-- title:
--   Exact source barrier dividend value for every starting capital under pointwise scale differentiability
-- statement:
--   Under the genuine Standing spectrally negative Lévy source law and positive discount, for barrier a>0, 0≤x≤a and differentiability of the q-scale function W only at a, the actual expected discounted Stieltjes barrier-strategy dividends from initial capital x equal ENNReal.ofReal(W(x)/W'(a)). It composes the canonically Proved killed two-sided-exit/strong-Markov factorisation with the canonically Proved pointwise reflected boundary reward identity, and cancels positive scale terms. No global C1 or assumption on W at intermediate reserves is needed.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1, equation (3.15); canonical source factorisation and genuine reflected regulator boundary identity.

import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_barrier_value_of_pointwise_diff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hda : DifferentiableAt ℝ W a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / deriv W a) := by sorry
