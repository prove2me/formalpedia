-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_boundary_reward_limit_strict_pos_finite
-- name    : AvramDividend.Classical.avram_wave3_02_boundary_reward_limit_strict_pos_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:25:07.197816+00:00
-- url     : https://prove2.me/theorems/0f82e126-9dc8-41aa-a119-7fd3dee4d9ac
-- title:
--   Genuine reflected Stieltjes dividend value has a strictly positive finite large-barrier limit
-- statement:
--   For a Standing original spectrally negative Levy process and positive discount, the genuine killed reflected-supremum Stieltjes reward has a strictly positive and finite limit as the drawdown cap tends to infinity. Source-verified monotonicity and the cap-independent bound establish convergence and finiteness; the already accepted strictly positive boundary reward at cap 1 establishes positivity. No scale derivative or global C1 is used.
-- source:
--   Avram Palmowski Pistorius (2007), positive stopped Stieltjes reflection reward, derivative-free monotonicity and Esscher uniform bound.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_boundary_reward
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_barrierSupValue_pos

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_boundary_reward_limit_strict_pos_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ L : ENNReal, 0 < L ∧ L < ⊤ ∧
      Tendsto (fun a : ℝ => barrierSupValue X a q) atTop (𝓝 L) := by sorry
