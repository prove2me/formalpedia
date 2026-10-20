-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_zero_reserve_bidirectional_scale_payoff_limit
-- name    : AvramDividend.Classical.chat03_zero_reserve_bidirectional_scale_payoff_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:58:32.915345+00:00
-- url     : https://prove2.me/theorems/8c9baee9-c119-4fec-9283-48f9c692be64
-- title:
--   Bidirectional sampled-reserve convergence of discounted scale payoffs at a zero passage reserve
-- statement:
--   At a stopping time with reserve exactly zero, suppose W(0)=0. For any sequence of observation times approaching this stopping time from the right, and any continuous discount factor, the sampled discounted q-scale payoffs converge to the continuous stopped payoff. Sampled reserves need not have an eventual sign and may oscillate across zero. This uses the separately proved continuity of W at zero given W(0)=0.
-- source:
--   Uses the published standalone zero-extension continuity lemma (conditional W0=0), official Levy right continuity and pinned Mathlib filter-product convergence. Does not establish killed harmonicity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_zero_extension_continuous_at_zero
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Monoid.Defs

open MeasureTheory Filter Set Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_zero_reserve_bidirectional_scale_payoff_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (τ : ℝ≥0) (clock : ℕ → ℝ≥0)
    (hclock : Tendsto clock atTop (𝓝[Set.Ici τ] τ))
    (discount : ℝ≥0 → ℝ) (hdiscount : ContinuousAt discount τ)
    (hreserveZero : x + X.X τ ω = 0) :
    Tendsto
      (fun n : ℕ => discount (clock n) * W (x + X.X (clock n) ω))
      atTop (𝓝 (discount τ * W (x + X.X τ ω))) := by sorry
