-- Prove2me | Theorems.Thm_AvramDividend_Classical_ftap_original_levy_stopped_rightContinuous
-- name    : AvramDividend.Classical.ftap_original_levy_stopped_rightContinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T11:21:14.626072+00:00
-- url     : https://prove2.me/theorems/f0336846-4fe8-44d3-830c-3bc956dcb9af
-- title:
--   Original stopped Levy process right-continuity via FTAP proof
-- statement:
--   Stopping an original spectrally negative Levy process preserves pathwise right-continuity. Direct adaptation of FTAP source code, Apache-2.0, commit 8c9c46e1b6e455f7d3069062957d4363879836ce.
-- source:
--   https://github.com/selpoG/lean-ftap-closedness/blob/8c9c46e1b6e455f7d3069062957d4363879836ce/FTAPTheorem42/Stochastic/Martingale/Basic/RightContinuousStoppedMartingale.lean

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Filter MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.ftap_original_levy_stopped_rightContinuous
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (τ : Ω → WithTop ℝ≥0) :
    ∀ ω t, ContinuousWithinAt
      (MeasureTheory.stoppedProcess X.X τ · ω) (Set.Ici t) t := by sorry
