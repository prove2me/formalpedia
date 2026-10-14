-- Prove2me | Theorems.Thm_ActuarialValuation_crMixture_nonnegative
-- name    : ActuarialValuation.crMixture_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:33:53.666054+00:00
-- url     : https://prove2.me/theorems/2d210c66-7584-48c5-b6d3-6224fcb15395
-- title:
--   Actual finite loss distributions and scenario ambiguity: crMixture_nonnegative
-- statement:
--   Convex probability mixtures have nonnegative scenario masses.
--
--   Mathematical relation:
--
--   $$
--   crMixture\_nonnegative
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 22, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://doi.org/10.1111/1467-9965.00068. The proposed model is rooted in Promislow chapter 22. The target Lean identity is an original derivation, not a verbatim published result. Published source page 412 gives the actuarial risk assessment chapter context; the Lean statement is an original derived target.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crMixWeights

namespace ActuarialValuation

theorem crMixture_nonnegative {n : ℕ} (p q : Fin n→ℝ) (mix : ℝ) (hl0 : 0≤mix) (hl1 : mix≤1) (hp : ∀ i,0≤p i) (hq : ∀ i,0≤q i) (j : Fin n) : 0≤crMixWeights p q mix j := by sorry

end ActuarialValuation
