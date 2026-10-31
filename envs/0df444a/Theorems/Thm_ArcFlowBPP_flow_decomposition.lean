-- Prove2me | Theorems.Thm_ArcFlowBPP_flow_decomposition
-- name    : ArcFlowBPP.flow_decomposition
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:08:49.058042+00:00
-- url     : https://prove2.me/theorems/9bf5c9d8-f8b0-4a1a-a909-f1b2fd567aaf
-- title:
--   §3, p.8 — flows in the acyclic arc-flow graph decompose into $s$–$t$ paths
-- statement:
--   Let $G$ be a finite labelled multigraph that is acyclic and has no directed walk from $t$ to $s$. Let $f \ge 0$ be a flow on the arcs satisfying the flow conservation constraints (18) with value $z$. Then there are finitely many paths $\pi_1, \dots, \pi_n$ from $s$ to $t$ and weights $w_1, \dots, w_n \ge 0$ such that
--
--   $$
--   f_a = \sum_{j=1}^n w_j \cdot \#\{\text{occurrences of } a \text{ in } \pi_j\} \quad \text{for every arc } a, \qquad \sum_{j=1}^n w_j = z.
--   $$
--
--   The statement has two clauses: one for real flows, and one for integer flows, where the weights $w_j$ are also integers.
--
--   This is the step that turns an arc-flow solution into a packing solution, one bin per unit of path weight, and it is the first half of the proof of Property 1.
--
--   **Formalization Note** Paths are lists of arcs (`IsWalk`), and occurrences are counted with `List.count`. The constraints (19)–(21) play no role here.
--
--   Differences from the source:
--   - reading: s is the source vertex and t the target, "the only excess node (node s)" and "the only deficit node (node t)" (p.8) → no directed walk from t to s (IsArcFlowGraph, second clause); reason: implied by s having no entering arc, by t having no leaving arc, and in an acyclic graph by the existence of any s–t path; without it an arc t → s with no s–t path makes the arc-flow relaxation unbounded below (z < 0) while Gilmore–Gomory has value 0 for b = 0
--   - encoding: (18): inflow − outflow = −z at s, z at t, 0 elsewhere → inflow k + [k = s]·z = outflow k + [k = t]·z for every vertex k; reason: avoids (truncated) subtraction so that one constraint serves ℕ and ℝ; equivalent to (18) when s ≠ t, which the standing assumptions imply
--   - encoding: paths from s to t in a directed acyclic graph → lists of arcs forming a directed walk from s to t (IsWalk); acyclic = no closed walk of positive length; reason: in an acyclic graph every walk is a path; same objects
--   - encoding: integer program and its linear relaxation → two clauses, one over ℕ and one over ℝ with f ≥ 0; reason: Lean convention; same programs
--   - generalization: finite vertex set V → arbitrary vertex type V with a finite arc type A; reason: only vertices incident to arcs matter; a finite V is a special case
-- source:
--   Brandão, Pedroso, Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression, arXiv:1310.6887v1, §3, p.8 (flow decomposition paragraph)

import Mathlib
import Definitions.Def_ArcFlowBPP_LabelledGraph
import Definitions.Def_ArcFlowBPP_IsWalk
import Definitions.Def_ArcFlowBPP_IsAcyclic
import Definitions.Def_ArcFlowBPP_IsArcFlowGraph
import Definitions.Def_ArcFlowBPP_FlowConservation

namespace ArcFlowBPP

/-- Brandão, Pedroso, *Bin Packing and Related Problems: General Arc-flow Formulation with Graph Compression*, arXiv:1310.6887v1, §3, p.8: "Flow decomposition properties (see, e.g., Ahuja et al. 1993) ensure that
non-negative flows can be represented by paths and cycles. Since we require an acyclic graph,
any valid flow can be decomposed into directed paths connecting the only excess node (node s)
to the only deficit node (node t)."

For a finite labelled graph satisfying the standing assumptions (acyclic, no walk from `t` to
`s`), every flow `f ≥ 0` satisfying the conservation constraints (18) with value `z` is a
nonnegative combination `f = ∑ⱼ wⱼ · χ(πⱼ)` of finitely many `s`–`t` paths `πⱼ`, where
`χ(π) a` is the number of occurrences of the arc `a` in `π`, with total weight `∑ⱼ wⱼ = z`.
The first clause is the real (linear-relaxation) case; the second is the integer case, with
integer weights.

**Formalization Note.** A "valid flow" is a flow satisfying (18) and (22); (19)–(21) play no
role. The paths are lists of arcs (`ArcFlowBPP.IsWalk`), and occurrences are counted with
`List.count`. -/
theorem flow_decomposition {m : ℕ} {V A : Type*} [Fintype A] [DecidableEq A] [DecidableEq V]
    (G : LabelledGraph m V A) (hG : IsArcFlowGraph G) :
    (∀ (f : A → ℝ) (z : ℝ), (∀ a, 0 ≤ f a) → FlowConservation G f z →
      ∃ (n : ℕ) (π : Fin n → List A) (w : Fin n → ℝ),
        (∀ j, IsWalk G G.s (π j) G.t) ∧ (∀ j, 0 ≤ w j) ∧
        (∀ a, f a = ∑ j, w j * ((π j).count a : ℝ)) ∧ ∑ j, w j = z) ∧
    (∀ (f : A → ℕ) (z : ℕ), FlowConservation G f z →
      ∃ (n : ℕ) (π : Fin n → List A) (w : Fin n → ℕ),
        (∀ j, IsWalk G G.s (π j) G.t) ∧
        (∀ a, f a = ∑ j, w j * (π j).count a) ∧ ∑ j, w j = z) := by sorry

end ArcFlowBPP
