-- Prove2me | Theorems.Thm_CSPIdealMem_lemma_4_1
-- name    : CSPIdealMem.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T08:31:05.964436+00:00
-- url     : https://prove2.me/theorems/c9e8b2c1-d734-4d6f-bccc-a005f5a99500
-- title:
--   Lemma 4.1 — bipartite edge spans
-- statement:
--   Let $G$ be a finite bipartite graph with vertex classes $A$, $B$ and edge set $E$, and $L=\mathrm{span}_{\mathbb Q}\{(e_a,e_b): ab\in E\}$. A vector $(u,v)\in\mathbb Q^A\times\mathbb Q^B$ belongs to $L$ if and only if
--
--   1. every isolated vertex has coordinate zero: $u_a=0$ for isolated $a\in A$ and $v_b=0$ for isolated $b\in B$; and
--   2. for the vertex set $K$ of every connected component containing at least one edge,
--   $$
--   \sum_{a\in A\cap K}u_a=\sum_{b\in B\cap K}v_b.
--   $$
--
--   It gives the explicit equations for each pair of blocks in the matrix $A_P$.
--
--   Differences from the source:
--   - encoding: a finite bipartite graph G with disjoint vertex sets A, B and edge set E → edgeGraph E, the simple graph on A ⊕ B with inl a ~ inr b iff (a, b) ∈ E, for finite types A, B and E ⊆ A × B; reason: every finite bipartite graph with given classes is of this form
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), Lemma 4.1, p.23 (PDF 23)

import Mathlib
import Definitions.Def_CSPIdealMem_RowsAP

namespace CSPIdealMem

open Classical in
/-- Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109), Lemma 4.1 (bipartite edge spans), p.23 (PDF 23).

Let `G` be a finite bipartite graph with vertex classes `A`, `B` and edge set `E`, and
`L := span_ℚ {(e_a, e_b) : ab ∈ E}`. Then `(u, v) ∈ ℚ^A × ℚ^B` belongs to `L` iff (1) every
isolated vertex has coordinate zero, and (2) in every connected component `K` containing an edge,
`∑_{a ∈ A ∩ K} u_a = ∑_{b ∈ B ∩ K} v_b`. -/
theorem lemma_4_1 {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (E : Set (A × B)) (u : A → ℚ) (v : B → ℚ) :
    (u, v) ∈ edgeSpan E ↔
      ((∀ a : A, (∀ w, ¬ (edgeGraph E).Adj (Sum.inl a) w) → u a = 0) ∧
        (∀ b : B, (∀ w, ¬ (edgeGraph E).Adj (Sum.inr b) w) → v b = 0)) ∧
      ∀ K : (edgeGraph E).ConnectedComponent,
        (∃ x y, (edgeGraph E).Adj x y ∧ (edgeGraph E).connectedComponentMk x = K) →
        ∑ a ∈ Finset.univ.filter (fun a => (edgeGraph E).connectedComponentMk (Sum.inl a) = K),
            u a =
          ∑ b ∈ Finset.univ.filter (fun b => (edgeGraph E).connectedComponentMk (Sum.inr b) = K),
            v b := by sorry

end CSPIdealMem
