-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_tendsto_initial
-- name    : AvramDividend.Classical.chat04_positive_reserve_killed_scale_tendsto_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:58:45.85646+00:00
-- url     : https://prove2.me/theorems/55db0a3f-13b3-48de-b0ba-f88494d7887f
-- title:
--   Positive-reserve history-killed discounted scale payoff tends to its initial value
-- statement:
--   For any spectrally negative Lévy path and a positive starting reserve, the ENNReal discounted q-scale reward killed by whole-history negative reserve converges to ENNReal.ofReal(W x) as the horizon approaches zero. The survival indicator equals the identity locally in time, and the underlying real discounted scale reward converges by right-continuity and scale-function continuity at positive arguments.
-- source:
--   Proved positive_reserve_killed_scale_unmasked_near_zero 9126cb3d-8bba-4edc-8dee-400bb7621089 and pending positive_reserve_discounted_scale_tendsto_initial 4940fc29-8b89-4aff-bca8-2fe2a173c6b0. Direct starting-time continuity input to Open killed q-scale renewal identity a885f0b3-3960-424d-97e4-abbcffe268ba.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_discounted_scale_tendsto_initial
import Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_killed_scale_unmasked_near_zero
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LeftRightNhds

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_positive_reserve_killed_scale_tendsto_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) (ω : Ω) :
    Filter.Tendsto
      (fun t : ℝ≥0 =>
        ({u : Ω | ∀ s : ℝ≥0, s ≤ t → 0 ≤ x + X.X s u}).indicator
          (fun u => ENNReal.ofReal
            (Real.exp (-(q * (t : ℝ))) * W (x + X.X t u))) ω)
      (𝓝 0) (𝓝 (ENNReal.ofReal (W x))) := by sorry
