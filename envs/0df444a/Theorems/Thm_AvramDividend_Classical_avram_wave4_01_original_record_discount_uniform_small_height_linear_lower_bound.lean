-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_uniform_small_height_linear_lower_bound
-- name    : AvramDividend.Classical.avram_wave4_01_original_record_discount_uniform_small_height_linear_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T15:36:40.125985+00:00
-- url     : https://prove2.me/theorems/10b785dc-9eb2-447d-b804-9d127cfabaf2
-- title:
--   Uniform linear lower envelope for genuine killed first-record discount over all drawdown depths above a positive cutoff
-- statement:
--   For actual Lévy first-record T_h and reflected drawdown ruin D_a in pure infinite small-negative-jump variation, fix a strictly positive depth cutoff delta. Simultaneously for every a>=delta and h>0, the actual discount E[e^{-qT_h}; T_h<D_a] is at least 1-h W'(delta)/W(delta). This uniform first-order estimate follows from the proven antitonicity of the genuine source hazard/log-scale slope and the exact uncapped exponential first-record law, using exp(-x)>=1-x. It provides a depth-uniform quantitative form of small-height convergence without Standing or a stochastic axiom.
-- source:
--   Proved source log-slope antitonicity a398acb7-0547-4203-ab8c-679e6359175f, genuine exponential record discount 1c71a04d-268a-4126-b1bd-c0537bda0db1, exact pinned Mathlib Real.add_one_le_exp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_unbounded_scale_logderiv_antitone_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_record_discount_uniform_small_height_linear_lower_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (δ a h : ℝ) (hδ : 0 < δ) (hδa : δ ≤ a) (hh : 0 < h) :
    1 - h * (deriv W δ / W δ) ≤
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal := by sorry
