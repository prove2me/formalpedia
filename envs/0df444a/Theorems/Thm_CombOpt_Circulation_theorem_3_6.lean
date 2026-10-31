-- Prove2me | Theorems.Thm_CombOpt_Circulation_theorem_3_6
-- name    : CombOpt.Circulation.theorem_3_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:05:19.200326+00:00
-- url     : https://prove2.me/theorems/1fb40ef1-205f-4c44-ba20-92ea48bf458b
-- title:
--   Theorem 3.6 — optimality iff no augmenting path (corrected: $r\ne s$)
-- statement:
--   Let $r\neq s$. A feasible $(r,s)$-flow $x$ is maximum if and only if there is no $x$-augmenting path.
--
--   Differences from the source:
--   - correction: r and s are not required to differ → hypothesis r ≠ s; reason: false for r = s: on any digraph take x = 0; it is maximum, since every flow has value 0, but the one-node path is an x-augmenting (r, r)-path
--   - encoding: capacities are nonnegative reals or ∞ → u : E → ℝ≥0∞; x_e is compared with u_e in EReal; reason: Lean type of exactly that range; no instance changes
--   - encoding: a path is a sequence of nodes and arcs → a list of arcs with a direction flag, from a given first node; reason: the flag makes forward and reverse explicit; same paths
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 3.6, p. 41

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_IsFeasibleFlow
import Definitions.Def_CombOpt_Circulation_IsMaximumFlow
import Definitions.Def_CombOpt_Circulation_IsAugmentingPath

open scoped ENNReal

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Theorem 3.6**, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), p. 41 (PDF p. 50): a feasible flow `x` is maximum if and only if there
is no `x`-augmenting path.

**Formalization Note** Corrected from the book by `r ≠ s`: for `r = s` the one-node path is an
`x`-augmenting `(r, r)`-path for every `x`, while `x = 0` is maximum. -/
theorem theorem_3_6 (G : MultiDigraph V E) (u : E → ℝ≥0∞) {r s : V} (hrs : r ≠ s) {x : E → ℝ}
    (hx : IsFeasibleFlow G u r s x) :
    IsMaximumFlow G u r s x ↔ ¬ ∃ p, IsAugmentingPath G u x r s p := by sorry

end CombOpt.Circulation
