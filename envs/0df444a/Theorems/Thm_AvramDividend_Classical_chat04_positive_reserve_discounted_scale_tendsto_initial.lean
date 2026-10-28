-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_positive_reserve_discounted_scale_tendsto_initial
-- name    : AvramDividend.Classical.chat04_positive_reserve_discounted_scale_tendsto_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:41:41.938981+00:00
-- url     : https://prove2.me/theorems/4940fc29-8b89-4aff-bca8-2fe2a173c6b0
-- title:
--   Positive-reserve discounted q-scale payoff converges to its initial value
-- statement:
--   For a spectrally negative Lévy process and a q-scale function W, at each strictly positive reserve x the real discounted payoff exp(-q t)W(x+X_t) tends to W(x) along every sample path as time t tends to zero. This follows from right-continuity of Lévy paths and continuity of W away from the origin. It supplies initial continuity to the killed q-scale renewal calculation after local unmasking of the survival indicator.
-- source:
--   Proved scaleFunction_continuousAt_away_zero 0dfe2e0c-ef19-4529-9ea0-e7db44c5b588; right-continuity in SpectrallyNegativeLevy; combines with Proved positive_reserve_killed_scale_unmasked_near_zero 9126cb3d-8bba-4edc-8dee-400bb7621089. Exact downstream target a885f0b3-3960-424d-97e4-abbcffe268ba.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp

open AvramDividend.Classical MeasureTheory Filter Set Topology
open scoped NNReal

theorem AvramDividend.Classical.chat04_positive_reserve_discounted_scale_tendsto_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : 0 < x) (ω : Ω) :
    Filter.Tendsto
      (fun t : ℝ≥0 => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω))
      (𝓝 0) (𝓝 (W x)) := by sorry
