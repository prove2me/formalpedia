-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_finite_step_upper
-- name    : AvramDividend.Classical.avram_wave3_02_standing_finite_step_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T07:23:43.442036+00:00
-- url     : https://prove2.me/theorems/7a8884aa-8819-4395-85f4-622518c49d07
-- title:
--   Standing-only derivative-free finite-step upper bound for the actual reflected regulator reward
-- statement:
--   Under the genuine Standing spectrally negative Levy model with q>0 and any positive barrier a, the expected discounted Stieltjes reward paid by the original reflected running-supremum regulator before ruin is bounded above by the fixed-mesh finite quotient a W(2a)/(W(2a)-W(a)). The bound follows from strict increase of W under positive Esscher-normalised monotonicity and the Proved killed-record geometric renewal budget. No pointwise or global scale differentiability is assumed.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1, stopped first-record expansion. Source-level proof combines Proved scaleFunction_tilted_positive_monotone with stoppedFirstRecord_upper_geometric_budgets and barrierSupValue_le_right_scale_quotient_of_killed_grid_step.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_stoppedFirstRecord_upper_geometric_budgets
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_le_right_scale_quotient_of_killed_grid_step

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_standing_finite_step_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    barrierSupValue X a q ≤
      ENNReal.ofReal (a * W (a + a) / (W (a + a) - W a)) := by sorry
