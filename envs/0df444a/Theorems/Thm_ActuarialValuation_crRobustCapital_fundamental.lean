-- Prove2me | Theorems.Thm_ActuarialValuation_crRobustCapital_fundamental
-- name    : ActuarialValuation.crRobustCapital_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:42:19.798978+00:00
-- url     : https://prove2.me/theorems/7c23e4fe-a23c-4386-a287-1491024caae6
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRobustCapital_fundamental
-- statement:
--   The capstone establishes the four coherent actuarial loss-risk axioms for a genuinely scenario-dependent two-law robust premium, plus its dominance over every convex mixture of the candidate probability distributions.
--
--   Mathematical relation:
--
--   $$
--   crRobustCapital\_fundamental
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crPortfolioLoss
import Definitions.Def_actuarial_crMixWeights

namespace ActuarialValuation

theorem crRobustCapital_fundamental {n : ℕ} (p q X Y : Fin n→ℝ) (c k mix : ℝ) (hp : ∀ i,0≤p i) (hq : ∀ i,0≤q i) (hpn : (∑ i : Fin n,p i)=1) (hqn : (∑ i : Fin n,q i)=1) (hXY : ∀ i,X i≤Y i) (hc : 0≤c) (hl0 : 0≤mix) (hl1 : mix≤1) : (crScenarioRisk p q X≤crScenarioRisk p q Y) ∧ (crScenarioRisk p q (fun i=>X i+k)=crScenarioRisk p q X+k) ∧ (crScenarioRisk p q (fun i=>c*X i)=c*crScenarioRisk p q X) ∧ (crScenarioRisk p q (crPortfolioLoss X Y)≤crScenarioRisk p q X+crScenarioRisk p q Y) ∧ (crExpected (crMixWeights p q mix) X≤crScenarioRisk p q X) := by sorry

end ActuarialValuation
