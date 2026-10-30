-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_all_capital_of_local_deriv_nonzero
-- name    : AvramDividend.Classical.avram_wave3_02_all_capital_of_local_deriv_nonzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:04:51.368996+00:00
-- url     : https://prove2.me/theorems/ce2e021b-91a4-4006-ab10-d8db52e039d8
-- title:
--   Original reflected barrier value at every capital from a nonzero local scale derivative
-- statement:
--   For Standing spectrally negative Lévy and any positive barrier with nonzero scale-function derivative, the actual reflected-barrier strategy discounted dividend value equals the scale-function barrierValue at all nonnegative initial capitals, including x=0, x=a and x>a.
-- source:
--   Avram–Palmowski–Pistorius 2007 Proposition 1. Uses Proved first-upcrossing Stieltjes exit factor and stopped renewal, exact ENNReal scale division, genuine initial-excess reflection above barrier, and boundary value at x=a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_above_value_of_boundary
import Theorems.Thm_AvramDividend_Classical_barrierValue_at_positive_barrier_eq_deriv_ratio
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Theorems.Thm_AvramDividend_Classical_barrierValue_nonnegative_at_nonnegative_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_all_capital_of_local_deriv_nonzero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hNe : deriv W a ≠ 0) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (barrierValue W a x) := by sorry
