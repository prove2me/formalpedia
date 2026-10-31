-- Prove2me | Theorems.Thm_CombOpt_MinCut_theorem_3_36_nonadjacent
-- name    : CombOpt.MinCut.theorem_3_36_nonadjacent
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:02:50.576292+00:00
-- url     : https://prove2.me/theorems/75766026-020d-41fe-bf1c-492cc9fd49de
-- title:
--   Proof of Theorem 3.36, p. 75 — if $v_{n-1},v_n$ are not adjacent, $u(\delta(v_n))\le\lambda(G;v_{n-2},v_n)$ and $u(\delta(v_n))\le\lambda(G;v_{n-2},v_{n-1})$
-- statement:
--   Let $G=(V,E)$ be a finite multigraph with capacities $u_e\ge0$, let $n\ge3$, and let $v_1,\dots,v_n$ be a legal ordering of the nodes of $G$ in which $v_{n-1}$ and $v_n$ are not adjacent (no edge has ends $v_{n-1},v_n$). Then
--
--   $$u(\delta(v_n))\le\lambda(G;v_{n-2},v_n)\qquad\text{and}\qquad u(\delta(v_n))\le\lambda(G;v_{n-2},v_{n-1}).$$
--
--   Together with Lemma 3.37 (applied to $p=v_n$, $q=v_{n-1}$, $r=v_{n-2}$) these two bounds give Theorem 3.36 in the non-adjacent case.
--
--   Differences from the source:
--   - generalization: capacities $u_e>0$ (p. 72) → $u_e\ge0$; reason: the book's argument (deleting a node can only decrease cut capacities, and $u(\delta(v_{n-1}))\ge u(\delta(V_{n-2})\cap\delta(v_{n-1}))$) uses only nonnegativity; positive capacities are an instance.
--   - encoding: the ordering $v_1,\dots,v_n$ → a bijection `σ : Fin n ≃ V` with `σ k` $=v_{k+1}$, so $v_n,v_{n-1},v_{n-2}$ are `σ (n-1)`, `σ (n-2)`, `σ (n-3)`, and the hypothesis $n\ge3$ makes $v_{n-2}$ exist; reason: Lean indexing; same instances.
--   - encoding: $\lambda(G;\cdot,\cdot)$ real → values in $\mathbb R\cup\{+\infty\}$; reason: the nodes involved are distinct, so the values are finite and equal to the book's.
--   - generalization: $G$ connected (setting of §3.5, p. 72) → any finite multigraph; reason: p. 75 proves Theorem 3.36, and so this step of its proof, "without this assumption"; connected graphs are an instance.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), proof of Theorem 3.36, display, p. 75 (PDF p. 84); both bounds proved on pp. 75–76 (PDF pp. 84–85)

import Mathlib
import Definitions.Def_CombOpt_MinCut_CapGraph
import Definitions.Def_CombOpt_MinCut_CapGraph_uSum
import Definitions.Def_CombOpt_MinCut_CapGraph_delta
import Definitions.Def_CombOpt_MinCut_CapGraph_minCutValue
import Definitions.Def_CombOpt_MinCut_CapGraph_IsLegalOrdering

namespace CombOpt.MinCut

/-- **Proof of Theorem 3.36, the non-adjacent case: the two inequalities.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), proof of
Theorem 3.36, p. 75 (PDF p. 84): "Now suppose that v_{n−1}, vₙ are not adjacent in G. In view of
Lemma 3.37, it will be enough to show that u(δ(vₙ)) ≤ λ(G; v_{n−2}, vₙ) and that
u(δ(vₙ)) ≤ λ(G; v_{n−2}, v_{n−1})." (Both are proved on pp. 75–76.)

Let `G` be a finite multigraph with nonnegative capacities, `n ≥ 3`, and `v₁, …, vₙ` a legal
ordering of its nodes in which `v_{n−1}` and `vₙ` are not joined by an edge. Then
`u(δ(vₙ)) ≤ λ(G; v_{n−2}, vₙ)` and `u(δ(vₙ)) ≤ λ(G; v_{n−2}, v_{n−1})`.

**Formalization Note.** The ordering is `σ : Fin n ≃ V` with `σ k = v_{k+1}`, so
`vₙ = σ (n−1)`, `v_{n−1} = σ (n−2)`, `v_{n−2} = σ (n−3)`. "Not adjacent" is: no edge has ends
`{v_{n−1}, vₙ}`. The capacities are `≥ 0` (the book has `> 0`, p. 72). `λ` lies in `WithTop ℝ`; the
nodes are distinct, so both values are finite. -/
theorem theorem_3_36_nonadjacent {V E : Type*} [Fintype V] [Fintype E] (G : CapGraph V E)
    (hu : ∀ e, 0 ≤ G.u e) {n : ℕ} (hn : 3 ≤ n) (σ : Fin n ≃ V) (hσ : G.IsLegalOrdering σ)
    (hna : ∀ e, G.ends e ≠ s(σ ⟨n - 2, by omega⟩, σ ⟨n - 1, by omega⟩)) :
    ((G.uSum (G.delta {σ ⟨n - 1, by omega⟩}) : ℝ) : WithTop ℝ) ≤
        G.minCutValue (σ ⟨n - 3, by omega⟩) (σ ⟨n - 1, by omega⟩) ∧
      ((G.uSum (G.delta {σ ⟨n - 1, by omega⟩}) : ℝ) : WithTop ℝ) ≤
        G.minCutValue (σ ⟨n - 3, by omega⟩) (σ ⟨n - 2, by omega⟩) := by sorry

end CombOpt.MinCut
