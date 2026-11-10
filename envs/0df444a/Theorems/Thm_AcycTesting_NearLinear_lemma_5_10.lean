-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_5_10
-- name    : AcycTesting.NearLinear.lemma_5_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:35:00.642805+00:00
-- url     : https://prove2.me/theorems/f4474893-99e3-4eea-98ec-320861758f65
-- title:
--   Lemma 5.10 — the complete blow-up is simple, multiplies degrees by t and fas by t², and is answerable by one query to G
-- statement:
--   Let $G$ be a simple directed graph on a finite set $V$ of $m$ vertices and let $t\ge1$. The complete blow-up $G^{(t)}$ has vertex set $V\times[t]$ and an edge $(u,i)\to(v,j)$ for every edge $u\to v$ of $G$ and all $i,j\in[t]$. Then $G^{(t)}$ is simple, has $tm$ vertices, and every outdegree and every indegree is multiplied by $t$:
--   $$\deg^+_{G^{(t)}}(u,i)=t\deg^+_G(u),\qquad \deg^-_{G^{(t)}}(u,i)=t\deg^-_G(u).$$
--   Moreover,
--   $$\mathrm{fas}(G^{(t)})=t^2\,\mathrm{fas}(G),\tag{5.14}$$
--   and one whole-vertex query to $G$ answers any whole-vertex query to $G^{(t)}$: there is a fixed map $\mathrm{sim}$, the same for all graphs, with $N^+_{G^{(t)}}((u,i))=\mathrm{sim}(N^+_G(u))$.
--
--   Differences from the source:
--   - encoding: copies (u, 1), …, (u, t) → vertex type V × Fin t (0-based copies); reason: Lean convention; the same graphs
--   - encoding: G simple on m vertices → a Fintype V (m = card V) and G : OutGraph V with IsLoopless G; reason: OutGraph has at most one edge per ordered pair by construction
--   - encoding: each directional degree is multiplied by t → outdeg (blowUp G t) (u, i) = t · outdeg G u and indeg (blowUp G t) (u, i) = t · indeg G u for all u, i; reason: the two directional degrees
--   - encoding: one whole-vertex query to G suffices to answer any whole-vertex query to G^(t) → ∃ sim : Finset V → Finset (V × Fin t) with blowUp H t (u, i) = sim (H u) for every graph H and all u, i; reason: the answer at (u, i) is a fixed function of the answer at u
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 23 (PDF 26), Lemma 5.10

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_Digraphs

namespace AcycTesting.NearLinear

/-- Lemma 5.10 (complete blow-up). -/
theorem lemma_5_10 {V : Type*} [Fintype V] [DecidableEq V] (G : OutGraph V)
    (hG : IsLoopless G) (t : ℕ) (ht : 1 ≤ t) :
    IsLoopless (blowUp G t) ∧
      Fintype.card (V × Fin t) = t * Fintype.card V ∧
      (∀ (u : V) (i : Fin t), outdeg (blowUp G t) (u, i) = t * outdeg G u ∧
        indeg (blowUp G t) (u, i) = t * indeg G u) ∧
      fas (blowUp G t) = t ^ 2 * fas G ∧
      ∃ sim : Finset V → Finset (V × Fin t),
        ∀ (H : OutGraph V) (u : V) (i : Fin t), blowUp H t (u, i) = sim (H u) := by sorry

end AcycTesting.NearLinear
