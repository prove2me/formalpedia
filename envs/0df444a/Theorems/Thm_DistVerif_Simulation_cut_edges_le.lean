-- Prove2me | Theorems.Thm_DistVerif_Simulation_cut_edges_le
-- name    : DistVerif.Simulation.cut_edges_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T13:23:52.290053+00:00
-- url     : https://prove2.me/theorems/16a1dee3-9e62-440a-bdb6-de999bcb5461
-- title:
--   §3.3 — at most $dp$ edges join $V\setminus R_{t-1}$ to $R_t$ (and $V\setminus L_{t-1}$ to $L_t$)
-- statement:
--   Let $G(\Gamma,d,p)$ be the network of §3.1 with its $i$-left and $i$-right sets $L_i$, $R_i$, and let $t$ be an integer with
--   $$0<t<\frac{d^p-1}{2}.$$
--   Then at most $d\cdot p$ edges of $G(\Gamma,d,p)$ join a vertex of $V\setminus R_{t-1}$ to a vertex of $R_t$, and at most $d\cdot p$ edges join a vertex of $V\setminus L_{t-1}$ to a vertex of $L_t$.
--
--   The paper states this observation in the sentence preceding Lemma 3.4, and identifies the edges in its proof: all edges linking vertices in $R_t$ and $V\setminus R_{t-1}$ are of the form $(u^\ell(R_t),u')$ where $u^\ell(R_t)$ is the leftmost level-$\ell$ tree vertex in $R_t$ and $u'$ one of its $d$ children, for $\ell=0,\dots,p-1$. The bound is what limits the information crossing from Alice's side to Bob's side in one round to $dp$ messages, independently of the number $\Gamma$ of paths.
--
--   **Formalization Note** Edges are counted as ordered pairs $(w,u)$ with $w$ outside $R_{t-1}$ (resp. $L_{t-1}$) and $u\in R_t$ (resp. $L_t$). Since $R_t\subseteq R_{t-1}$, at most one orientation of an edge qualifies, so this is the number of edges. The hypotheses $0<t$ (so that $t-1$ is a genuine predecessor) and the strict inequality, written in $\mathbb R$, are those of Lemma 3.4.
-- source:
--   Das Sarma, Holzer, Kor, Korman, Nanongkai, Pandurangan, Peleg, Wattenhofer, Distributed Verification and Hardness of Distributed Approximation, SIAM J. Comput. 41 (2012), p. 1249, §3.3, sentence before Lemma 3.4 ("there are at most dp edges between vertices in V \ R_{t−1} (V \ L_{t−1}, respectively) and vertices in R_t (L_t, respectively)"); edge form identified in the proof of Lemma 3.4, p. 1250

import Mathlib
import Definitions.Def_DistVerif_Simulation_Network

namespace DistVerif.Simulation

/-- **§3.3, sentence before Lemma 3.4** (p. 1249). For `0 < t < (d^p - 1)/2`, at most `d·p`
edges of `G(Γ, d, p)` join a vertex of `V \ R_{t-1}` to a vertex of `R_t`, and at most `d·p`
join a vertex of `V \ L_{t-1}` to a vertex of `L_t`. Edges are counted as ordered pairs
`(w, u)` with `w` outside and `u` inside; since `R_t ⊆ R_{t-1}` (and `L_t ⊆ L_{t-1}`), each
edge contributes at most one such pair. -/
theorem cut_edges_le (Γ d p t : ℕ) (ht0 : 0 < t) (ht : (t : ℝ) < ((d : ℝ) ^ p - 1) / 2) :
    (Finset.univ.filter fun q : Vtx Γ d p × Vtx Γ d p =>
        (graph Γ d p).Adj q.1 q.2 ∧ q.1 ∉ R Γ d p (t - 1) ∧ q.2 ∈ R Γ d p t).card ≤ d * p ∧
    (Finset.univ.filter fun q : Vtx Γ d p × Vtx Γ d p =>
        (graph Γ d p).Adj q.1 q.2 ∧ q.1 ∉ L Γ d p (t - 1) ∧ q.2 ∈ L Γ d p t).card ≤ d * p := by sorry

end DistVerif.Simulation
