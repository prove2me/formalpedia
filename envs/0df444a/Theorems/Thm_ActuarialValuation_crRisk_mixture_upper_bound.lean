-- Prove2me | Theorems.Thm_ActuarialValuation_crRisk_mixture_upper_bound
-- name    : ActuarialValuation.crRisk_mixture_upper_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:57.167973+00:00
-- url     : https://prove2.me/theorems/90da4562-296e-4058-98be-a900f9f2bb97
-- title:
--   Coherent worst-case actuarial premium and portfolio: crRisk_mixture_upper_bound
-- statement:
--   Worst-case premium upper-bounds all convex mixtures of the two plausible probability laws.
--
--   Mathematical relation:
--
--   $$
--   crRisk\_mixture\_upper\_bound
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crExpected
import Definitions.Def_actuarial_crMixWeights
import Definitions.Def_actuarial_crScenarioRisk

namespace ActuarialValuation

theorem crRisk_mixture_upper_bound {n : ℕ} (p q X : Fin n→ℝ) (mix : ℝ) (hl0 : 0≤mix) (hl1 : mix≤1) : crExpected (crMixWeights p q mix) X ≤ crScenarioRisk p q X := by sorry

end ActuarialValuation
