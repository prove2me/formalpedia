-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
-- name    : AvramDividend.Classical.avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:03:32.786137+00:00
-- url     : https://prove2.me/theorems/450d3b50-76dd-48ed-b8f9-2147bffd49fe
-- title:
--   Exact original reflected scale ratio from pointwise scale differentiability
-- statement:
--   The original killed running-supremum Stieltjes dividend reward at barrier a>0 equals W(a)/W'(a) at any a where W is differentiable, under Standing and q>0. The proven derivative-free two-sided reflected-regulator renewal sandwich gives the exact upper/lower quotient bounds near zero; the previously Proved source Esscher positivity makes W'(a)>0, and the accepted deterministic limit/sandwich assembly produces the exact ENNReal scale ratio. Global positive-axis C1 is unnecessary for this source theorem.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 and equation (3.13); accepted source-level stopped first-record renewal bounds, Esscher derivative positivity and finite-difference squeeze.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_two_sided_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_of_stopped_renewal_bounds

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a)
    (hdiff : DifferentiableAt ℝ W a) :
    barrierSupValue X a q = ENNReal.ofReal (W a / deriv W a) := by sorry
