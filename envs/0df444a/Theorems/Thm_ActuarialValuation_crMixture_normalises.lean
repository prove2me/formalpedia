-- Prove2me | Theorems.Thm_ActuarialValuation_crMixture_normalises
-- name    : ActuarialValuation.crMixture_normalises
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:40.059557+00:00
-- url     : https://prove2.me/theorems/4cda676b-bf06-421b-869b-14659a2be3a8
-- title:
--   Actual finite loss distributions and scenario ambiguity: crMixture_normalises
-- statement:
--   A convex or affine mixture of two probability distributions preserves total mass one.
--
--   Mathematical relation:
--
--   $$
--   crMixture\_normalises
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crMixWeights

namespace ActuarialValuation

theorem crMixture_normalises {n : ℕ} (p q : Fin n→ℝ) (mix : ℝ) (hp : (∑ i : Fin n,p i)=1) (hq : (∑ i : Fin n,q i)=1) : (∑ i : Fin n, crMixWeights p q mix i)=1 := by sorry

end ActuarialValuation
