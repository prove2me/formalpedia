-- Prove2me | Theorems.Thm_CombOpt_Circulation_theorem_3_7
-- name    : CombOpt.Circulation.theorem_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:05:03.164373+00:00
-- url     : https://prove2.me/theorems/e9ecbf1c-84ff-4018-b924-14667f9aa3d8
-- title:
--   Theorem 3.7 — integral maximum flows
-- statement:
--   If the capacity vector $u$ is integral, meaning that its finite components are integers, and there exists a maximum $(r,s)$-flow, then there exists a maximum $(r,s)$-flow that is integral.
--
--   Differences from the source:
--   - encoding: capacities are nonnegative reals or ∞ → u : E → ℝ≥0∞; x_e is compared with u_e in EReal; reason: Lean type of exactly that range; no instance changes
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 3.7, p. 42

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_IsMaximumFlow
import Definitions.Def_CombOpt_Circulation_IsIntegralVector
import Definitions.Def_CombOpt_Circulation_IsIntegralBound

open scoped ENNReal

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Theorem 3.7**, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), p. 42 (PDF p. 51): if `u` is integral and there exists a maximum flow,
then there exists a maximum flow that is integral.

**Formalization Note** "`u` is integral" concerns the finite components only (p. 39), which is
`IsIntegralBound` of the coercion of `u` to `EReal`. -/
theorem theorem_3_7 (G : MultiDigraph V E) (u : E → ℝ≥0∞) (r s : V)
    (hu : IsIntegralBound fun e => (u e : EReal)) (hmax : ∃ x, IsMaximumFlow G u r s x) :
    ∃ x, IsMaximumFlow G u r s x ∧ IsIntegralVector x := by sorry

end CombOpt.Circulation
