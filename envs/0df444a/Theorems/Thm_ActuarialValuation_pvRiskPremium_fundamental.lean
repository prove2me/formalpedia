-- Prove2me | Theorems.Thm_ActuarialValuation_pvRiskPremium_fundamental
-- name    : ActuarialValuation.pvRiskPremium_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:24:51.116233+00:00
-- url     : https://prove2.me/theorems/ccdc6d8d-7956-4156-aaff-2ecc03f4b1b9
-- title:
--   Actual loss distribution and percentile premium adequacy: pvRiskPremium_fundamental
-- statement:
--   The capstone connects the expected-loss equivalence premium to an actual scenario distribution of prospective loss and proves monotone percentile adequacy under a nonnegative premium annuity and a specified solvency probability threshold.
--
--   Mathematical relation:
--
--   $$
--   pvRiskPremium\_fundamental
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 15 and 16, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/globalassets/assets/files/edu/fall2006webcatalog.pdf. Published source page 235 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pvExpectedLoss
import Definitions.Def_actuarial_pvEquivalencePremium
import Definitions.Def_actuarial_pvAdequacy
import Definitions.Def_actuarial_pvCdf
import Definitions.Def_actuarial_pvLoss
import Definitions.Def_actuarial_pvExpected

namespace ActuarialValuation

theorem pvRiskPremium_fundamental {n : ℕ} (p benefit annuity : Fin n → ℝ) (P Q α : ℝ) (hmean : pvExpected p annuity ≠ 0) (hp : ∀ i, 0 ≤ p i) (hnorm : (∑ i : Fin n, p i) = 1) (ha : ∀ i, 0 ≤ annuity i) (hPQ : P ≤ Q) (hα : α ≤ pvAdequacy p benefit annuity P) : (pvExpectedLoss p benefit annuity (pvEquivalencePremium p benefit annuity) = 0) ∧ (pvAdequacy p benefit annuity P = pvCdf p (pvLoss benefit annuity P) 0) ∧ (α ≤ pvAdequacy p benefit annuity Q) := by sorry

end ActuarialValuation
