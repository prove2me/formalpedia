-- Prove2me | Theorems.Thm_ArcFlowBPP_gg_exact_to_af
-- name    : ArcFlowBPP.gg_exact_to_af
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:08:09.989574+00:00
-- url     : https://prove2.me/theorems/a50c1abc-d72f-4ad9-a2e3-e956c678d4ec
-- title:
--   Proof of Property 1, p.7 — an exactly covering Gilmore–Gomory solution gives an arc-flow solution
-- statement:
--   Let $G$ be a finite labelled multigraph with $s$–$t$ path patterns $P(G)$, and $b$ demands. Let $x \ge 0$ be a solution of the Gilmore–Gomory model over $P(G)$ that meets every demand exactly, $\sum_p p_i\, x_p = b_i$ for every item $i$. Then there is a flow $f$ such that $(f, \sum_p x_p)$ is feasible for the arc-flow model (17)–(22) for **every** exact-demand set $J$, the arc upper bounds (21) included.
--
--   This holds for the integer programs and for their linear relaxations (two clauses). It is the substitution of the patterns by flows in the proof of Property 1, read from the patterns back to the flow.
--
--   Differences from the source:
--   - encoding: (18): inflow − outflow = −z at s, z at t, 0 elsewhere → inflow k + [k = s]·z = outflow k + [k = t]·z for every vertex k; reason: avoids (truncated) subtraction so that one constraint serves ℕ and ℝ; equivalent to (18) when s ≠ t, which the standing assumptions imply
--   - encoding: paths from s to t in a directed acyclic graph → lists of arcs forming a directed walk from s to t (IsWalk); acyclic = no closed walk of positive length; reason: in an acyclic graph every walk is a path; same objects
--   - encoding: items 1, …, m; loss arcs carry label i = 0 → items Fin m; arc labels Option (Fin m), loss arcs labelled none; reason: Lean convention; same instances
--   - encoding: integer program and its linear relaxation → two clauses, one over ℕ and one over ℝ with f ≥ 0; reason: Lean convention; same programs
--   - generalization: a directed acyclic graph whose paths from s to t correspond to the valid packing patterns → any finite labelled multigraph (no acyclicity or other graph hypothesis); reason: the flow built from s–t paths satisfies (18)–(22) in every graph; the paper's graphs are a special case
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, proof of Property 1, p.7

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph
import Definitions.Def_ArcFlowBPP_IsWalk
import Definitions.Def_ArcFlowBPP_pattern
import Definitions.Def_ArcFlowBPP_pathPatterns
import Definitions.Def_ArcFlowBPP_FlowConservation
import Definitions.Def_ArcFlowBPP_labelFlow
import Definitions.Def_ArcFlowBPP_ArcFlowFeasible
import Definitions.Def_ArcFlowBPP_coverage
import Definitions.Def_ArcFlowBPP_numRolls

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, proof of Property 1, p.7: "we can substitute (18), (21) and (22) by the patterns and
obtain the classical model", read from the patterns back to the flow.

The direction from Gilmore–Gomory to the arc-flow model: let `x ≥ 0` be a solution of the
Gilmore–Gomory model over the path patterns `P(G)` that meets every demand exactly,
`∑_p pᵢ x_p = bᵢ` for all `i`. Then there is a flow `f` such that `(f, ∑_p x_p)` is feasible for
(17)–(22) for **every** exact-demand set `J`, including the arc upper bounds (21). The first
clause is the integer case, the second the linear relaxation.

**Formalization Note.** The flow is the sum, over the patterns `p`, of `x_p` times an `s`–`t`
path with pattern `p`; no acyclicity is needed for this direction. -/
theorem gg_exact_to_af {m : ℕ} {V A : Type*} [Fintype A] [DecidableEq V]
    (G : LabelledGraph m V A) (b : Fin m → ℕ) (J : Finset (Fin m)) :
    (∀ x : (Fin m → ℕ) →₀ ℕ, ↑x.support ⊆ pathPatterns G → (∀ i, coverage x i = b i) →
      ∃ f : A → ℕ, ArcFlowFeasible ℕ G b J f (numRolls x)) ∧
    (∀ x : (Fin m → ℕ) →₀ ℝ, ↑x.support ⊆ pathPatterns G → (∀ p, 0 ≤ x p) →
      (∀ i, coverage x i = (b i : ℝ)) →
      ∃ f : A → ℝ, ArcFlowFeasible ℝ G b J f (numRolls x)) := by sorry

end ArcFlowBPP
