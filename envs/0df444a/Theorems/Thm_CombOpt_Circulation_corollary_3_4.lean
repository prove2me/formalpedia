-- Prove2me | Theorems.Thm_CombOpt_Circulation_corollary_3_4
-- name    : CombOpt.Circulation.corollary_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:15.895223+00:00
-- url     : https://prove2.me/theorems/a17c0e1d-30fc-4a61-ae7e-58d02415ff1f
-- title:
--   Corollary 3.4 — a cut capacity bounds every flow value
-- statement:
--   For any feasible $(r,s)$-flow $x$ and any $(r,s)$-cut $\delta(R)$,
--
--   $$
--   f_x(s)\le u(\delta(R)),
--   $$
--
--   where $u(\delta(R))=\sum_{e\in\delta(R)}u_e$ may be $\infty$. This is the easy direction of the max-flow min-cut theorem.
--
--   Differences from the source:
--   - encoding: capacities are nonnegative reals or ∞ → u : E → ℝ≥0∞; x_e is compared with u_e in EReal; reason: Lean type of exactly that range; no instance changes
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Corollary 3.4, p. 40

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_delta
import Definitions.Def_CombOpt_Circulation_excess
import Definitions.Def_CombOpt_Circulation_IsFeasibleFlow

open scoped ENNReal

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Corollary 3.4**, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), p. 40 (PDF p. 49): for any feasible `(r, s)`-flow `x` and any
`(r, s)`-cut `δ(R)`, `f_x(s) ≤ u(δ(R))`.

**Formalization Note** `u(δ(R))` is summed in `ℝ≥0∞` and may be `∞`; the comparison is in `EReal`. -/
theorem corollary_3_4 (G : MultiDigraph V E) (u : E → ℝ≥0∞) {r s : V} {R : Finset V}
    (hr : r ∈ R) (hs : s ∉ R) {x : E → ℝ} (hx : IsFeasibleFlow G u r s x) :
    (excess G x s : EReal) ≤ ((∑ e ∈ delta G R, u e : ℝ≥0∞) : EReal) := by sorry

end CombOpt.Circulation
