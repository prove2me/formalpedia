-- Prove2me | Theorems.Thm_ActuarialValuation_multistate_cashflow_fundamental
-- name    : ActuarialValuation.multistate_cashflow_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T23:25:57.806068+00:00
-- url     : https://prove2.me/theorems/5e32d599-5bd0-4633-8709-bc865aa6cd43
-- title:
--   Fundamental multiple-state life-contingent cashflow valuation
-- statement:
--   Combines finite state-occupation and transition EPVs with homogeneity of the total contract value.
--
--   **Mathematical statement**
--
--   $$
--   V_n=V_n^{\rm occ}+V_n^{\rm tr},\qquad V_n(ab,ac)=aV_n(b,c)
--   $$
-- source:
--   Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 19 §19.2.2 equations (19.2)-(19.4) and §19.2.3 equation (19.6); Dickson, Hardy and Waters (2009), Actuarial Mathematics for Life Contingent Risks, Chapter 8 §§8.3-8.7, https://doi.org/10.1017/CBO9780511800146.009; Norris, Markov Chains (1997), Chapter 1 §1.1

import Mathlib
import Definitions.Def_actuarial_multiStateTermCashflowPV
import Definitions.Def_actuarial_occupationStageReward
import Definitions.Def_actuarial_transitionStageReward
open MeasureTheory

namespace ActuarialValuation

theorem multistate_cashflow_fundamental {S : Type*} [Fintype S] (μ : ℕ → S → ℝ) (P : ℕ → S → S → ℝ)
  (b : ℕ → S → S → ℝ) (c : ℕ → S → ℝ) (v : ℝ) (n : ℕ) (a : ℝ)
  :
  (multiStateTermCashflowPV μ P b c v n =
    (∑ k ∈ Finset.range n, v ^ k * occupationStageReward (μ k) (c k)) +
    (∑ k ∈ Finset.range n, v ^ (k + 1) * transitionStageReward (μ k) (P k) (b k)))
  ∧ (multiStateTermCashflowPV μ P
     (fun k i j => a * b k i j) (fun k i => a * c k i) v n =
       a * multiStateTermCashflowPV μ P b c v n) := by sorry

end ActuarialValuation
