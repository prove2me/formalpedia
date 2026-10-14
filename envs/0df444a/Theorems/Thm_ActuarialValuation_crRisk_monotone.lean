-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_monotone
-- name    : ActuarialValuation.crRisk_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:21.62202+00:00
-- url     : https://prove2.me/theorems/e8d952af-42bc-4f67-88d0-9f16d09c7d31
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_monotone
-- statement:
--   For two genuine candidate probability measures, scenario-wise larger losses produce no smaller robust premiums.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_monotone
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crScenarioRisk

namespace ActuarialValuation

theorem crRisk_monotone {n : ℕ} (p q X Y : Fin n→ℝ) (hp : ∀ i,0≤p i) (hq : ∀ i,0≤q i) (hXY : ∀ i,X i≤Y i) : crScenarioRisk p q X≤crScenarioRisk p q Y := by sorry

end ActuarialValuation
