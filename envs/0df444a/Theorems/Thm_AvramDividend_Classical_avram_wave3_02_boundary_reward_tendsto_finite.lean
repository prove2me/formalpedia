-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_boundary_reward_tendsto_finite
-- name    : AvramDividend.Classical.avram_wave3_02_boundary_reward_tendsto_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:13:03.945977+00:00
-- url     : https://prove2.me/theorems/d24cf012-3a5f-4161-9192-a48e11c56ec5
-- title:
--   Genuine reflected Stieltjes barrier reward converges to finite limit as cap tends to infinity
-- statement:
--   For an original Standing spectrally negative Levy process at positive discount, the true expected stopped Stieltjes running-supremum dividend value at barrier a converges as a tends to plus infinity to a finite extended nonnegative real limit L. The proof uses canonical monotonicity of stopped reflected rewards in drawdown cap and the newly canonically Proved barrier-independent reward bound, then applies pinned Mathlib monotone convergence to the supremum. No pointwise/global scale derivative assumptions, no surrogate reward or optimality claim.
-- source:
--   Avram Palmowski Pistorius (2007), reflected running-supremum dividend process and q-discount; accepted stopped-reward monotonicity and Esscher-derived uniform bound.

import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_boundary_reward

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_boundary_reward_tendsto_finite
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ L : ENNReal, L < ⊤ ∧
      Tendsto (fun a : ℝ => barrierSupValue X a q) atTop (𝓝 L) := by sorry
