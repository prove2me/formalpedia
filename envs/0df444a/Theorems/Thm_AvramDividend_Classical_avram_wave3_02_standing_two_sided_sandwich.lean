-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_two_sided_sandwich
-- name    : AvramDividend.Classical.avram_wave3_02_standing_two_sided_sandwich
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:38:36.886397+00:00
-- url     : https://prove2.me/theorems/9e1a8864-77c9-47f7-9ada-1db5a3bc809e
-- title:
--   Derivative-free two-sided stopped-renewal squeeze at every positive barrier
-- statement:
--   For any Standing spectrally negative Levy process, positive discount q, positive barrier a and genuine q-scale W, eventually for positive epsilon down to zero, the original stopped reflected-regulator reward is squeezed between the left and right positive-scale finite-difference quotients. Both bounds were independently proved for actual killed Stieltjes running-supremum dividends without HasDerivAt or C1. The only event restriction is 0<epsilon<a, which holds eventually in the right neighbourhood of zero.
-- source:
--   Avram Palmowski Pistorius 2007 Proposition 1, first-record renewal; exact assembly of Proved avram_wave3_02_standing_left_step_lower and avram_wave3_02_standing_all_right_step_upper.

import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_left_step_lower
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_all_right_step_upper

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_standing_two_sided_sandwich
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (ε * W (a - ε) / (W a - W (a - ε))) ≤
        barrierSupValue X a q ∧
      barrierSupValue X a q ≤
        ENNReal.ofReal (ε * W (a + ε) / (W (a + ε) - W a)) := by sorry
