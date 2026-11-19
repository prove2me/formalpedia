-- Prove2me | Theorems.Thm_BilateralProfitMHR_positive_density_profit_facts
-- name    : BilateralProfitMHR.positive_density_profit_facts
-- status  : Proved
-- author  : @sim2000dg
-- created : 2026-11-18T11:43:09.8262+00:00
-- url     : https://prove2.me/theorems/cea38126-7350-420a-94fc-785db873678d
-- title:
--   Profit and trade probabilities for independent positive densities
-- statement:
--   For independent seller and buyer valuations with strictly positive densities on $[0,1]$, the prior is a probability measure and the trade probability is measurable. On the unit square it factors as $F_S(p)(1-F_B(q))$. Expected profit is continuous, bounded in absolute value by one, and positive exactly in the open ordered triangle. Its positive global maximum is attained in that triangle. The result also gives the boundary identities, the product identity used to reconstruct trade probabilities from a split point, and the comparison of profit differences with differences in negative log profit.
-- source:
--   Brüstle, di Gregorio, Fusco and Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism, §2, Proposition 3.2 and the proof of Proposition 5.4.

import Mathlib
import Definitions.Def_BilateralProfitMHR_Model
open BilateralProfitMHR MeasureTheory BilateralProfit MechanismDesign.BilateralTrade

theorem BilateralProfitMHR.positive_density_profit_facts (E : Environment) (hE : UnitSupport E) :
    IsProbabilityMeasure E.prior ∧
    Measurable (Ptrade E.prior) ∧
    (∀ a, 0 ≤ Ptrade E.prior a ∧ Ptrade E.prior a ≤ 1) ∧
    (∀ a ∈ unitSq, Ptrade E.prior a = E.cdfS a.1 * (1 - E.cdfB a.2)) ∧
    MonotoneOn E.cdfS (Set.Icc 0 1) ∧
    MonotoneOn E.cdfB (Set.Icc 0 1) ∧
    ContinuousOn (muP E.prior) unitSq ∧
    ContinuousOn (lossL E.prior) intT ∧
    (∀ a ∈ unitSq, 0 < muP E.prior a ↔ a ∈ intT) ∧
    (0 < muStar E.prior ∧ muStar E.prior ≤ 1) ∧
    (∀ a ∈ unitSq, muP E.prior a ≤ muStar E.prior) ∧
    (∃ a ∈ intT, muP E.prior a = muStar E.prior) ∧
    (∀ a ∈ unitSq, |muP E.prior a| ≤ 1 ∧ muP E.prior a ≤ Ptrade E.prior a) ∧
    (∀ x ∈ Set.Icc (0:ℝ) 1, muP E.prior (0,x) = 0 ∧ muP E.prior (x,1) = 0 ∧
      muP E.prior (x,x) = 0) ∧
    (∀ x ∈ Set.Icc (0:ℝ) 1, ∀ z ∈ Set.Icc (0:ℝ) 1, ∀ y ∈ Set.Icc (0:ℝ) 1,
      x ≤ z → z ≤ y →
      Ptrade E.prior (x,z) * Ptrade E.prior (z,y) = Ptrade E.prior (x,y) * Ptrade E.prior (z,z) ∧
      Ptrade E.prior (x,z) ≤ Ptrade E.prior (z,z) ∧
      Ptrade E.prior (z,y) ≤ Ptrade E.prior (z,z) ∧
      Ptrade E.prior (x,y) ≤ Ptrade E.prior (z,z)) ∧
    (∀ a ∈ intT, ∀ b ∈ intT, muP E.prior a ≤ muP E.prior b →
      muP E.prior b - muP E.prior a ≤
        muStar E.prior * (lossL E.prior a - lossL E.prior b)) := by sorry
