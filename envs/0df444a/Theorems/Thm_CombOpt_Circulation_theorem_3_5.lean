-- Prove2me | Theorems.Thm_CombOpt_Circulation_theorem_3_5
-- name    : CombOpt.Circulation.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:52.27745+00:00
-- url     : https://prove2.me/theorems/b628a7d4-3012-474b-a3bf-e888579cee82
-- title:
--   Theorem 3.5 — Max-Flow Min-Cut Theorem (corrected: $r\ne s$)
-- statement:
--   Let $r\neq s$ be nodes of a digraph with capacities in $\mathbb R_{\ge0}\cup\{\infty\}$. If there is a maximum $(r,s)$-flow, then
--
--   $$
--   \max\{f_x(s): x\text{ a feasible }(r,s)\text{-flow}\}=\min\{u(\delta(R)):\delta(R)\text{ an }(r,s)\text{-cut}\},
--   $$
--
--   both extrema being attained. Zero and infinite capacities, parallel arcs and loops are all allowed.
--
--   **Formalization Note** The statement gives a value $c$ in the extended reals that is the greatest flow value and the least cut capacity.
--
--   Differences from the source:
--   - correction: r and s are not required to differ → hypothesis r ≠ s; reason: false for r = s: for any digraph every flow has value 0 and there is no (r, r)-cut, so the min is over the empty set
--   - encoding: capacities are nonnegative reals or ∞ → u : E → ℝ≥0∞; x_e is compared with u_e in EReal; reason: Lean type of exactly that range; no instance changes
--   - encoding: max = min → ∃ c, IsGreatest (flow values) c ∧ IsLeast (cut capacities) c, in EReal; reason: this says that both extrema exist and agree; the printed equation means the same
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 3.5, p. 41

import Mathlib
import Definitions.Def_CombOpt_Circulation_MultiDigraph
import Definitions.Def_CombOpt_Circulation_delta
import Definitions.Def_CombOpt_Circulation_excess
import Definitions.Def_CombOpt_Circulation_IsFeasibleFlow
import Definitions.Def_CombOpt_Circulation_IsMaximumFlow

open scoped ENNReal

namespace CombOpt.Circulation

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

/-- **Theorem 3.5 (Max-Flow Min-Cut Theorem)**, Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), p. 41 (PDF p. 50): if there is a maximum
`(r, s)`-flow, then `max {f_x(s) : x a feasible (r, s)-flow} = min {u(δ(R)) : δ(R) an (r, s)-cut}`.

**Formalization Note** The common value `c` is both the greatest flow value and the least cut
capacity, so both extrema are attained. It is compared in `EReal` because a cut capacity can be `∞`.
Corrected from the book by `r ≠ s`: for `r = s` there is no `(r, s)`-cut. -/
theorem theorem_3_5 (G : MultiDigraph V E) (u : E → ℝ≥0∞) {r s : V} (hrs : r ≠ s)
    (hmax : ∃ x, IsMaximumFlow G u r s x) :
    ∃ c : EReal,
      IsGreatest {c | ∃ x, IsFeasibleFlow G u r s x ∧ c = (excess G x s : EReal)} c ∧
      IsLeast {c | ∃ R : Finset V, r ∈ R ∧ s ∉ R ∧ c = ((∑ e ∈ delta G R, u e : ℝ≥0∞) : EReal)} c := by sorry

end CombOpt.Circulation
