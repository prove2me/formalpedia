-- Prove2me | Theorems.Thm_ArcFlowBPP_property_1
-- name    : ArcFlowBPP.property_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:09:01.065496+00:00
-- url     : https://prove2.me/theorems/fd225ada-fe8a-421a-96c2-584aab266f96
-- title:
--   Property 1 — the general arc-flow model is equivalent to Gilmore–Gomory over the path patterns
-- statement:
--   Let $m$ be the number of items, $b \in \mathbb N^m$ the demands and $J \subseteq \{1, \dots, m\}$ any set of items whose demands are to be met exactly. Let $G$ be a finite labelled multigraph with source $s$ and target $t$ that is acyclic, has no directed walk from $t$ to $s$, and whose set $P(G)$ of $s$–$t$ path patterns is closed under removing one item (as every set of valid packing patterns is). Then the general arc-flow model (17)–(22) on $G$ and the Gilmore–Gomory model (6)–(8) over the patterns $P(G)$ are equivalent:
--
--   1. their integer optimal values are equal,
--   $$
--   \min\{z : (f,z) \text{ feasible for (17)–(22), integer}\} \;=\; \min\Big\{\sum_{p \in P(G)} x_p : x \text{ feasible for (6)–(8) over } P(G)\Big\};
--   $$
--   2. their linear-relaxation values (lower bounds) are equal.
--
--   Infeasible programs have value $+\infty$, so both sides are infeasible together.
--
--   This is the correctness statement of the arc-flow formulation: solving the compact arc-flow model gives the same optimum, and its linear relaxation the same lower bound, as the exponentially large Gilmore–Gomory model over all valid packing patterns, for every choice of the exact-demand set $J$ and with the arc upper bounds (21).
--
--   Differences from the source:
--   - reading: model (17)-(22) is equivalent to the classical Gilmore-Gomory model (6)-(9) → equal integer optimal values and equal linear-relaxation values; reason: the proof derives the equivalence by Dantzig–Wolfe substitution and concludes "lower bounds provided by both models are the same"
--   - generalization: a graph with all valid packing patterns represented as paths from s to t (paths correspond to every valid packing pattern, p.7) → RemovalClosed (pathPatterns G): removing one item from a path pattern gives a path pattern or the zero pattern; reason: this is the property the proof uses ("replacing the use of some patterns by other patterns that do not include the items … satisfied with excess"); every set of valid packing patterns ((9), (25), also with x ≤ b) without the empty pattern is closed under removing one item, so the paper's hypothesis implies it
--   - reading: s is the source vertex and t the target, "the only excess node (node s)" and "the only deficit node (node t)" (p.8) → no directed walk from t to s (IsArcFlowGraph, second clause); reason: implied by s having no entering arc, by t having no leaving arc, and in an acyclic graph by the existence of any s–t path; without it an arc t → s with no s–t path makes the arc-flow relaxation unbounded below (z < 0) while Gilmore–Gomory has value 0 for b = 0
--   - encoding: items 1, …, m; loss arcs carry label i = 0 → items Fin m; arc labels Option (Fin m), loss arcs labelled none; reason: Lean convention; same instances
--   - encoding: (18): inflow − outflow = −z at s, z at t, 0 elsewhere → inflow k + [k = s]·z = outflow k + [k = t]·z for every vertex k; reason: avoids (truncated) subtraction so that one constraint serves ℕ and ℝ; equivalent to (18) when s ≠ t, which the standing assumptions imply
--   - encoding: paths from s to t in a directed acyclic graph → lists of arcs forming a directed walk from s to t (IsWalk); acyclic = no closed walk of positive length; reason: in an acyclic graph every walk is a path; same objects
--   - encoding: optimal values of the integer programs and their linear relaxations → infima in ℕ∞ (integer) and EReal (relaxation), ⊤ when infeasible; Gilmore–Gomory solutions are finitely supported functions on patterns; reason: Lean convention; the values coincide with the paper's whenever the programs are feasible, and infeasibility gives ⊤ on both sides
--   - generalization: finite vertex set V → arbitrary vertex type V with a finite arc type A; reason: only vertices incident to arcs matter; a finite V is a special case
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, Property 1, p.7, and its proof

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
import Definitions.Def_ArcFlowBPP_coverage
import Definitions.Def_ArcFlowBPP_numRolls
import Definitions.Def_ArcFlowBPP_GGFeasible
import Definitions.Def_ArcFlowBPP_afIP
import Definitions.Def_ArcFlowBPP_afLP
import Definitions.Def_ArcFlowBPP_ggIP
import Definitions.Def_ArcFlowBPP_ggLP

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, Property 1 (equivalence to the classical Gilmore-Gomory model), p.7: "For a graph
with all valid packing patterns represented as paths from s to t, model (17)-(22) is equivalent
to the classical Gilmore-Gomory model (6)-(9) with the same patterns as the ones obtained from
paths in the graph." With the proof's "From this equivalence follows that lower bounds provided
by both models are the same when the same set of patterns is considered."

For every number of items `m`, demands `b`, exact-demand set `J ⊆ {1, …, m}`, and every finite
labelled multigraph `G` that is acyclic, has no walk from the target `t` to the source `s`, and
whose set of `s`–`t` path patterns is closed under removing one item:
1. the integer optimum of the arc-flow model (17)–(22) equals the integer optimum of the
   Gilmore–Gomory model (6)–(8) over the path patterns of `G` (in `ℕ∞`, `⊤` if infeasible);
2. the linear-relaxation values of the two models are equal (in `EReal`).

**Formalization Note.** "Equivalent" is read, as in the proof, as equal integer optimal values
and equal linear-relaxation bounds. The hypothesis "all valid packing patterns represented as
paths" (paths ↔ valid patterns, p.7) is replaced by the weaker `RemovalClosed (pathPatterns G)`,
which every set of valid packing patterns satisfies. Items are `Fin m`, loss arcs have label
`none`, and (18) is written without subtraction (`ArcFlowBPP.FlowConservation`). -/
theorem property_1 {m : ℕ} {V A : Type*} [Fintype A] [DecidableEq V] (G : LabelledGraph m V A)
    (hG : IsArcFlowGraph G) (hP : RemovalClosed (pathPatterns G)) (b : Fin m → ℕ)
    (J : Finset (Fin m)) :
    afIP G b J = ggIP (pathPatterns G) b ∧ afLP G b J = ggLP (pathPatterns G) b := by sorry

end ArcFlowBPP
