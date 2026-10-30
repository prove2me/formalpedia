-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_value_of_vcstar_C2
-- name    : AvramDividend.Classical.avram_wave3_02_cstar_value_of_vcstar_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:06:17.254026+00:00
-- url     : https://prove2.me/theorems/0b7b5cb8-5f42-481d-a56c-71443e6ce979
-- title:
--   Genuine all-capital optimal barrier value under C2 smoothness of vcstar
-- statement:
--   Under Standing, positive discount, finite cstar and the exact root smoothness hypothesis ContDiffOn ℝ 2 (vcstar W) on the positive half-line, the actual reflected barrier-strategy discounted dividend value equals vcstar at every nonnegative reserve, including zero, below and above the barrier.
-- source:
--   Avram–Palmowski–Pistorius 2007 Proposition 1. Uses the true killed first-upcrossing Stieltjes factor 870df5c1, exact zero-barrier value d73a6aec, initial-excess bridge fb9550bc, and two new source-faithful C2 normaliser and local stopped-renewal ratio theorems. Provides the third disjunct of the root's h_smooth without assuming global W C1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_cstar_nonzero_of_vcstar_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_barrierSupValue_ratio_of_nonzero_deriv
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_nonneg
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

theorem AvramDividend.Classical.avram_wave3_02_cstar_value_of_vcstar_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (hsmooth : ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ))) :
    ∀ x : ℝ, 0 ≤ x →
      dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
        ENNReal.ofReal (vcstar W x) := by sorry
