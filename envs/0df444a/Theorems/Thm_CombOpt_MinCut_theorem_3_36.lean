-- Prove2me | Theorems.Thm_CombOpt_MinCut_theorem_3_36
-- name    : CombOpt.MinCut.theorem_3_36
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:37.630994+00:00
-- url     : https://prove2.me/theorems/b8a686e2-9ea8-450a-8d8c-4b35fd26b738
-- title:
--   Theorem 3.36 — in a legal ordering $v_1,\dots,v_n$, $\delta(v_n)$ is a minimum $(v_n,v_{n-1})$-cut
-- statement:
--   Let $G=(V,E)$ be a finite multigraph (loops and parallel edges allowed, not necessarily connected) with capacities $u_e\ge0$ and at least two nodes, and let $v_1,\dots,v_n$ be a legal ordering of $G$, i.e. with $V_i=\{v_1,\dots,v_i\}$,
--
--   $$u\bigl(\delta(V_{i-1})\cap\delta(v_i)\bigr)\ge u\bigl(\delta(V_{i-1})\cap\delta(v_j)\bigr)\qquad(2\le i<j\le n).$$
--
--   Then $\delta(v_n)$ is a minimum $(v_n,v_{n-1})$-cut of $G$: it separates $v_n$ from $v_{n-1}$, and
--
--   $$u(\delta(v_n))\le u(\delta(S))\qquad\text{for every } S\subseteq V \text{ containing exactly one of } v_n,v_{n-1}.$$
--
--   This is the theorem behind the Nagamochi–Ibaraki and Stoer–Wagner minimum cut algorithm: a legal ordering, computable like Prim's algorithm, yields a pair of nodes whose minimum separating cut is known without any flow computation, and identifying them reduces the global minimum cut problem to a smaller graph.
--
--   Differences from the source:
--   - generalization: capacities $u_e>0$ (p. 72) → $u_e\ge0$; reason: the proof (induction on edges and nodes, pp. 75–76) uses only nonnegativity; positive capacities are an instance.
--   - encoding: the ordering $v_1,\dots,v_n$ → a bijection `σ : Fin n ≃ V` with `σ k` $=v_{k+1}$, $v_n$ = `σ (n-1)`, $v_{n-1}$ = `σ (n-2)`, with the hypothesis $n\ge2$; reason: Lean indexing, and $n\ge2$ is the statement's presupposition that $v_{n-1}$ exists.
--   - encoding: "$\delta(v_n)$ is a minimum $(v_n,v_{n-1})$-cut", a property of an edge set → `IsMinCut` of the node set $\{v_n\}$: it separates the two nodes and $u(\delta(\{v_n\}))\le u(\delta(S))$ for every separating $S$; reason: the capacity of a cut depends only on its edge set, and $\delta(\{v_n\})$ is the star $\delta(v_n)$.
--   - generalization: $G$ connected (setting of the minimum cut problem, p. 72) → any finite multigraph; reason: p. 75: "Although we have assumed that $G$ is connected, it is convenient to prove Theorem 3.36 without this assumption"; connected graphs are an instance.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 3.36, p. 74 (PDF p. 83)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_IsMinCut
import Definitions.Def_CombOpt_MinCut_CapGraph_IsLegalOrdering

namespace CombOpt.MinCut

/-- **Theorem 3.36 (Nagamochi–Ibaraki, Stoer–Wagner; legal orderings).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Theorem 3.36, p. 74 (PDF p. 83): "If v₁, …, vₙ is a legal ordering of G, then δ(vₙ) is a minimum
(vₙ, v_{n−1})-cut of G."

Let `G` be a finite multigraph with nonnegative capacities and at least two nodes, and let
`v₁, …, vₙ` be a legal ordering of its nodes. Then the star `δ(vₙ)` separates `vₙ` from `v_{n−1}`
and `u(δ(vₙ)) ≤ u(δ(S))` for every `S ⊆ V` separating `vₙ` from `v_{n−1}`.

**Formalization Note.** The ordering is `σ : Fin n ≃ V` with `σ k = v_{k+1}`, so `vₙ = σ (n−1)` and
`v_{n−1} = σ (n−2)`; `2 ≤ n` makes `v_{n−1}` exist. `G` may have loops and parallel edges and need
not be connected (p. 75: "it is convenient to prove Theorem 3.36 without this assumption"). The
capacities are `≥ 0` (the book has `> 0`, p. 72). -/
theorem theorem_3_36 {V E : Type*} [Fintype V] [Fintype E] (G : CapGraph V E)
    (hu : ∀ e, 0 ≤ G.u e) {n : ℕ} (hn : 2 ≤ n) (σ : Fin n ≃ V) (hσ : G.IsLegalOrdering σ) :
    G.IsMinCut {σ ⟨n - 1, by omega⟩} (σ ⟨n - 1, by omega⟩) (σ ⟨n - 2, by omega⟩) := by sorry

end CombOpt.MinCut
