-- Prove2me | Theorems.Thm_ArcFlowBPP_lp_bound_without_20_21
-- name    : ArcFlowBPP.lp_bound_without_20_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:09:02.625999+00:00
-- url     : https://prove2.me/theorems/f40610b9-5354-404b-a688-d3610374d663
-- title:
--   Proof of Property 1, p.7 — (20) and (21) do not change the linear-relaxation bound
-- statement:
--   Let $G$ be a finite labelled multigraph that is acyclic, has no directed walk from $t$ to $s$, and whose set of $s$–$t$ path patterns is closed under removing one item. For any demands $b$ and any exact-demand set $J$, the linear-relaxation value of the arc-flow model (17)–(22) equals the linear-relaxation value of the model without the equality constraints (20) and the arc bounds (21):
--
--   $$
--   \inf\{z : (f,z) \text{ satisfies (18)–(22) with } f \ge 0 \text{ real}\} \;=\; \inf\Big\{z : (f, z) \text{ satisfies (18)},\ \sum_{(u,v,j):j=i} f_{uvj} \ge b_i \ \forall i,\ f \ge 0 \text{ real}\Big\}.
--   $$
--
--   Both values are taken in the extended reals.
--
--   Differences from the source:
--   - reading: s is the source vertex and t the target, "the only excess node (node s)" and "the only deficit node (node t)" (p.8) → no directed walk from t to s (IsArcFlowGraph, second clause); reason: implied by s having no entering arc, by t having no leaving arc, and in an acyclic graph by the existence of any s–t path; without it an arc t → s with no s–t path makes the arc-flow relaxation unbounded below (z < 0) while Gilmore–Gomory has value 0 for b = 0
--   - generalization: a graph with all valid packing patterns represented as paths from s to t (paths correspond to every valid packing pattern, p.7) → RemovalClosed (pathPatterns G): removing one item from a path pattern gives a path pattern or the zero pattern; reason: this is the property the proof uses ("replacing the use of some patterns by other patterns that do not include the items … satisfied with excess"); every set of valid packing patterns ((9), (25), also with x ≤ b) without the empty pattern is closed under removing one item, so the paper's hypothesis implies it
--   - encoding: (18): inflow − outflow = −z at s, z at t, 0 elsewhere → inflow k + [k = s]·z = outflow k + [k = t]·z for every vertex k; reason: avoids (truncated) subtraction so that one constraint serves ℕ and ℝ; equivalent to (18) when s ≠ t, which the standing assumptions imply
--   - encoding: paths from s to t in a directed acyclic graph → lists of arcs forming a directed walk from s to t (IsWalk); acyclic = no closed walk of positive length; reason: in an acyclic graph every walk is a path; same objects
--   - encoding: optimal values of the integer programs and their linear relaxations → infima in ℕ∞ (integer) and EReal (relaxation), ⊤ when infeasible; Gilmore–Gomory solutions are finitely supported functions on patterns; reason: Lean convention; the values coincide with the paper's whenever the programs are feasible, and infeasibility gives ⊤ on both sides
--   - generalization: finite vertex set V → arbitrary vertex type V with a finite arc type A; reason: only vertices incident to arcs matter; a finite V is a special case
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, proof of Property 1, p.7

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph
import Definitions.Def_ArcFlowBPP_IsWalk
import Definitions.Def_ArcFlowBPP_IsAcyclic
import Definitions.Def_ArcFlowBPP_IsArcFlowGraph
import Definitions.Def_ArcFlowBPP_pattern
import Definitions.Def_ArcFlowBPP_pathPatterns
import Definitions.Def_ArcFlowBPP_RemovalClosed
import Definitions.Def_ArcFlowBPP_FlowConservation
import Definitions.Def_ArcFlowBPP_labelFlow
import Definitions.Def_ArcFlowBPP_ArcFlowFeasible
import Definitions.Def_ArcFlowBPP_afLP

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, proof of Property 1, p.7: "The equality constraints (20) and the upper bound on
variable values (21) have no effect on the lower bounds, since for every optimal solution with
some excess there is a solution with the same objective value that satisfies the demand exactly".

For a finite labelled graph satisfying the standing assumptions whose path patterns are closed
under removing one item, and for any demands `b` and exact-demand set `J`, the linear-relaxation
value of (17)–(22) equals the linear-relaxation value of the arc-flow model without (20) and
(21): minimize `z` subject to (18), `∑_{label = i} f ≥ bᵢ` for every item `i`, and `f ≥ 0`.

**Formalization Note.** Both values are infima in `EReal` (`⊤` when infeasible). -/
theorem lp_bound_without_20_21 {m : ℕ} {V A : Type*} [Fintype A] [DecidableEq V]
    (G : LabelledGraph m V A) (hG : IsArcFlowGraph G) (hP : RemovalClosed (pathPatterns G))
    (b : Fin m → ℕ) (J : Finset (Fin m)) :
    afLP G b J =
      ⨅ (f : A → ℝ) (z : ℝ)
        (_ : FlowConservation G f z ∧ (∀ i, (b i : ℝ) ≤ labelFlow G f i) ∧ (∀ a, 0 ≤ f a)),
        (z : EReal) := by sorry

end ArcFlowBPP
