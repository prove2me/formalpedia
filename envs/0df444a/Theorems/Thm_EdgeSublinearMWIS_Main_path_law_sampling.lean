-- Prove2me | Theorems.Thm_EdgeSublinearMWIS_Main_path_law_sampling
-- name    : EdgeSublinearMWIS.Main.path_law_sampling
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-17T18:05:26.962225+00:00
-- url     : https://prove2.me/theorems/3675697b-f29e-422f-b87b-40e3f4547962
-- title:
--   Lemma 11 — finite path-law sampling
-- statement:
--   Let $G$ be a finite graph with costs $0\le x_v\le1$, total cost $k=\sum_vx_v$, and weighted edge energy $e_G(x)$. Suppose a finite law on simple paths in an active set $W$ has independent uniform ordered endpoints and vertex congestion at most $\ell x_v/k$, as in Lemma 8, with $\ell\ge1$. Let $H$ be any finite simple graph with $m_H>0$ edges. If $p>0$ satisfies
--   $$k\ge p,\qquad e_G(x)\le k^2/p,\qquad p\ge12m_H^2\ell^2,$$
--   then there is an induced almost-embedding $(\phi,\pi)$ of $H$ into $G$, with every vertex image and path in $W$, such that
--   $$\sum_{e\in E(H)}|V(\pi(e))|\le4\ell m_H.$$
--   This is the finite sampling step in the proof of Lemma 11. An almost-embedding permits coincident vertex images but requires paths for nonincident edges to be vertex-disjoint; being induced also forbids an edge between such paths.
--
--   **Formalization Note** The sampling argument is stated for an arbitrary finite source graph, with its edge count explicit in the budget. The source applies it to a subcubic source graph. The constant 12 is an explicit choice for the source's sufficiently large constant.
-- source:
--   Édouard Bonnet and Yeonsu Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, STOC 2027 submission #1044 (October 2026), proof of Lemma 11, p.10, Eqs. (8)–(10), and p.11 first paragraph, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Paths

open scoped BigOperators Classical

namespace EdgeSublinearMWIS.Main

theorem path_law_sampling {h n : ℕ} (H : SimpleGraph (Fin h)) (G : SimpleGraph (Fin n))
    (x : Fin n → ℝ) (ell : ℝ) (W : Finset (Fin n)) (f : List (List (Fin n) × ℝ))
    (hf : PathOutcome G x ell W f) (hell : 1 ≤ ell) (hx : ∀ v,0 ≤ x v ∧ x v ≤ 1)
    (p : ℝ) (hp : 0 < p) (hk : p ≤ vertexSum x Finset.univ)
    (henergy : edgeEnergy G x ≤ (vertexSum x Finset.univ)^2/p)
    (hbudget : 12*(Fintype.card (EdgeIndex H):ℝ)^2*ell^2 ≤ p)
    (hE : 0 < Fintype.card (EdgeIndex H)) :
    ∃ E : AlmostEmbedding H G,E.Induced ∧ (∀ v,E.vertex v∈W) ∧
      (∀ (e : EdgeIndex H) (v : Fin n),v∈E.path e → v∈W) ∧
      (∑ e : EdgeIndex H,((E.path e).length:ℝ)) ≤ 4*ell*Fintype.card (EdgeIndex H) := by sorry

end EdgeSublinearMWIS.Main
