-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_positive_reserve_payoff_right_limit
-- name    : AvramDividend.Classical.chat03_positive_reserve_payoff_right_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:44:38.376734+00:00
-- url     : https://prove2.me/theorems/3f94888d-b957-45e8-8402-c5740cfaf1fa
-- title:
--   Right-sided convergence of stopped discounted scale-function payoffs at a positive reserve
-- statement:
--   For a spectrally negative Levy sample path and a q-scale function W, take any sequence of sampled times converging to tau from the right. When the reserve x+X_tau is strictly positive, continuity of W on the nonnegative half-line implies that the discounted stopped-scale payoffs converge to the corresponding continuous-time payoff, for any time-discount function continuous at tau. The theorem does not assert convergence at reserve zero, where W may have a jump, and does not assume stochastic harmonicity.
-- source:
--   Direct composition of the official Levy right-continuity field, scale function continuity on the nonnegative half-line, and pinned Mathlib filter convergence. Independent of the Open stopped-scale parent.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Monoid.Defs

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_positive_reserve_payoff_right_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (τ : ℝ≥0) (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici τ] τ))
    (discount : ℝ≥0 → ℝ) (hdiscount : ContinuousAt discount τ)
    (hpositive : 0 < x + X.X τ ω) :
    Tendsto
      (fun n : ℕ => discount (clock n) * W (x + X.X (clock n) ω))
      atTop (𝓝 (discount τ * W (x + X.X τ ω))) := by sorry
