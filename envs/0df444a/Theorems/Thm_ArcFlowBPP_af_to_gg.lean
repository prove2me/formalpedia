-- Prove2me | Theorems.Thm_ArcFlowBPP_af_to_gg
-- name    : ArcFlowBPP.af_to_gg
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:08:40.193071+00:00
-- url     : https://prove2.me/theorems/3a078d40-f044-4223-968e-388422622881
-- title:
--   Proof of Property 1, p.7 — an arc-flow solution gives a Gilmore–Gomory solution of the same value
-- statement:
--   Let $G$ be a finite labelled multigraph that is acyclic and has no directed walk from $t$ to $s$, and let $P(G)$ be its set of $s$–$t$ path patterns. Let $b$ be demands and $J$ any exact-demand set. Every feasible solution $(f, z)$ of the arc-flow model (17)–(22) yields a feasible solution $x$ of the Gilmore–Gomory model (6)–(8) over $P(G)$ with the same objective value:
--
--   $$
--   \sum_{p \in P(G)} x_p = z .
--   $$
--
--   This holds for the integer programs and for their linear relaxations (two clauses). It gives the inequalities "Gilmore–Gomory optimum $\le$ arc-flow optimum" for both the integer optimum and the linear-relaxation bound.
--
--   Differences from the source:
--   - reading: s is the source vertex and t the target, "the only excess node (node s)" and "the only deficit node (node t)" (p.8) → no directed walk from t to s (IsArcFlowGraph, second clause); reason: implied by s having no entering arc, by t having no leaving arc, and in an acyclic graph by the existence of any s–t path; without it an arc t → s with no s–t path makes the arc-flow relaxation unbounded below (z < 0) while Gilmore–Gomory has value 0 for b = 0
--   - encoding: (18): inflow − outflow = −z at s, z at t, 0 elsewhere → inflow k + [k = s]·z = outflow k + [k = t]·z for every vertex k; reason: avoids (truncated) subtraction so that one constraint serves ℕ and ℝ; equivalent to (18) when s ≠ t, which the standing assumptions imply
--   - encoding: paths from s to t in a directed acyclic graph → lists of arcs forming a directed walk from s to t (IsWalk); acyclic = no closed walk of positive length; reason: in an acyclic graph every walk is a path; same objects
--   - encoding: items 1, …, m; loss arcs carry label i = 0 → items Fin m; arc labels Option (Fin m), loss arcs labelled none; reason: Lean convention; same instances
--   - encoding: integer program and its linear relaxation → two clauses, one over ℕ and one over ℝ with f ≥ 0; reason: Lean convention; same programs
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
import Definitions.Def_ArcFlowBPP_FlowConservation
import Definitions.Def_ArcFlowBPP_labelFlow
import Definitions.Def_ArcFlowBPP_ArcFlowFeasible
import Definitions.Def_ArcFlowBPP_coverage
import Definitions.Def_ArcFlowBPP_numRolls
import Definitions.Def_ArcFlowBPP_GGFeasible

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, proof of Property 1, p.7: "Extending Valério de Carvalho’s proof, we apply
Dantzig-Wolfe decomposition to model (17)-(22) keeping (17), (19) and (20) in the master problem
and (18), (21) and (22) in the subproblem. As the subproblem is a flow model that will only
generate patterns resulting from paths in the graph, we can substitute (18), (21) and (22) by
the patterns and obtain the classical model."

The direction from the arc-flow model to Gilmore–Gomory: for a finite labelled graph satisfying
the standing assumptions, every feasible solution `(f, z)` of (17)–(22), for any demands `b` and
any exact-demand set `J`, yields a feasible solution `x` of the Gilmore–Gomory model (6)–(8)
over the path patterns `P(G)` with the same objective value `∑_p x_p = z`. The first clause is
the integer case, the second the linear relaxation. -/
theorem af_to_gg {m : ℕ} {V A : Type*} [Fintype A] [DecidableEq V] (G : LabelledGraph m V A)
    (hG : IsArcFlowGraph G) (b : Fin m → ℕ) (J : Finset (Fin m)) :
    (∀ (f : A → ℕ) (z : ℕ), ArcFlowFeasible ℕ G b J f z →
      ∃ x : (Fin m → ℕ) →₀ ℕ, GGFeasible ℕ (pathPatterns G) b x ∧ numRolls x = z) ∧
    (∀ (f : A → ℝ) (z : ℝ), ArcFlowFeasible ℝ G b J f z →
      ∃ x : (Fin m → ℕ) →₀ ℝ, GGFeasible ℝ (pathPatterns G) b x ∧ numRolls x = z) := by sorry

end ArcFlowBPP
