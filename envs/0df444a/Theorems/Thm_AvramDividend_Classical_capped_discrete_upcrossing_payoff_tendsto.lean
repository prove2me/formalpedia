-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_discrete_upcrossing_payoff_tendsto
-- name    : AvramDividend.Classical.capped_discrete_upcrossing_payoff_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T10:18:42.969047+00:00
-- url     : https://prove2.me/theorems/d9c9194b-b16d-4d4b-8a0c-82f6d1919d89
-- title:
--   Capped first-upcrossing discounts converge to the unrestricted infinite-grid first-passage discount
-- statement:
--   For a real sequence u(k), nondecreasing NNReal grid clock c(k), threshold z and real discount q, consider K_m=hittingBtwn u (Ioi z) 0 m as the first strict upper crossing with cap m. The discounted reward 1_{u(K_m)>z} exp(-q c(K_m)) converges in ENNReal as m→∞ to exp(-q T) on T<∞ and zero otherwise, where T is the ENNReal infimum of clock(k) over every strict sampled upper crossing. If there is no crossing both rewards vanish. If there is one, Nat.find gives the first index j; the capped hitting indices equal j for all m≥j and T=c(j) by monotonicity. This is the exact deterministic limit needed to pass one-sided Lévy grid cap inequalities to infinite discrete passage times through Fatou.

import Mathlib.Probability.Process.HittingTime
import Mathlib.Data.Nat.Find
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.capped_discrete_upcrossing_payoff_tendsto
    (u : ℕ → ℝ) (clock : ℕ → ℝ≥0) (hc : Monotone clock)
    (z q : ℝ) [DecidablePred (fun k : ℕ => z < u k)] :
    Tendsto
      (fun m : ℕ =>
        let K := hittingBtwn (fun k (_ : Unit) => u k) (Ioi z) 0 m ()
        if z < u K then ENNReal.ofReal
          (Real.exp (-(q * (clock K : ℝ)))) else 0) atTop
      (𝓝 (let T : ℝ≥0∞ :=
        ⨅ k : ℕ, if z < u k then (clock k : ℝ≥0∞) else ∞
        if T < ∞ then ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal T))) else 0)) := by sorry
