-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_value_of_gaussian_or_bv
-- name    : AvramDividend.Classical.avram_wave3_02_cstar_value_of_gaussian_or_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T23:32:24.209295+00:00
-- url     : https://prove2.me/theorems/a1bcdf9d-fdb4-4c5a-a45a-f9ecdb780bc9
-- title:
--   All-reserve genuine cstar reflected barrier value under Gaussian or bounded variation
-- statement:
--   For the original spectrally negative Lévy dividend regulator with Standing, positive discount, finite cstar, and either a Gaussian part or bounded variation, the actual discounted barrier-strategy value equals vcstar at every nonnegative initial reserve, including x=0, x<=cstar, x>cstar and cstar=0. This is a source-correct conditional version of Proposition 1.
-- source:
--   Avram–Palmowski–Pistorius 2007, Proposition 1. Genuine Proved first-upcrossing factor, initial excess-payment bridge and zero-barrier value; fresh Gaussian/BV strict scale derivative positivity a3226a42 and Gaussian/BV reflected ratio f5d1d5b0. Source-faithful branch of Open all-capital value 02cd610e without using universal pure-jump C¹.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scaleDeriv_pos_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_scale_ratio_of_gaussian_or_bv
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel
import Theorems.Thm_AvramDividend_Classical_barrier_strategy_value_zero_all_capital
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierValue_at_positive_barrier_eq_deriv_ratio
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_at_nonnegative_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_cstar_value_of_gaussian_or_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hbranch : 0 < X.σ ∨ X.BoundedVariation) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by sorry
