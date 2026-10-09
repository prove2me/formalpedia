-- Prove2me | Theorems.Thm_CClosedGraphs_Improved_case_2_count
-- name    : CClosedGraphs.Improved.case_2_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:22:46.817041+00:00
-- url     : https://prove2.me/theorems/ab3668d6-7672-4a10-9c41-2b5e0748c5a2
-- title:
--   Inequality (4) and its consequence, p. 10 — cliques meeting N(v) ∪ {v} number at most F₀(Δ, c−1) min{Δ, n/Δ} 2^c
-- statement:
--   Let $c\ge2$, let $G[W]$ be $c$-closed with $n=|W|$ vertices, let $\Delta\ge1$ bound the degree in $G[W]$ of every vertex of $W$, and let $v\in W$ have degree exactly $\Delta$ in $G[W]$, and assume $\Delta>\sqrt n$ (Case 2). Assume the inductive hypothesis at level $c-1$: every non-empty vertex set $W'$ with $G[W']$ $(c-1)$-closed satisfies $\mathrm{mc}(G[W'])\le F_0(|W'|,c-1)$. Then the number of maximal cliques of $G[W]$ that contain at least one vertex of $N(v)\cup\{v\}$ satisfies
--   $$\#\{K \text{ maximal clique of } G[W] : K\cap(N(v)\cup\{v\})\ne\emptyset\}\;<\;F_0(\Delta,c-1)\,\min\Big\{\Delta,\frac{n}{\Delta}\Big\}\,2^{c}.$$
--
--   This combines inequality (4), $|\mathcal K|\le\min\{\Delta,n/\Delta\}2^{c-1}F_0(\Delta,c-1)$, with the bound $F_0(\Delta,c-1)$ on the cliques through $v$. It is the high-degree step of the recurrence for $F(n,c)$.
--
--   **Formalization Note** The inductive hypothesis is an explicit premise and requires $W'$ non-empty: the empty graph has one maximal clique while $F_0(0,c-1)=0$. All quantities on the right are real numbers; $n/\Delta$ is real division.
-- source:
--   Fox, Roughgarden, Seshadhri, Wei and Wein, Finding cliques in social networks: a new distribution-free model, arXiv:1804.07431v1, p. 10, proof of Theorem 3.1, Case 2, inequality (4) and the display after it

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

namespace CClosedGraphs.Improved
open Classical in
theorem case_2_count {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ} (hc : 2 ≤ c)
    {G : SimpleGraph V} {W : Set V} (hW : IsCClosedOn c G W) {v : V} (hv : v ∈ W)
    (Δ : ℕ) (hΔpos : 1 ≤ Δ) (hΔ : ∀ x ∈ W, (W ∩ G.neighborSet x).ncard ≤ Δ)
    (hv_deg : (W ∩ G.neighborSet v).ncard = Δ)
    (hcase : Real.sqrt (W.ncard : ℝ) < (Δ : ℝ))
    (hIH : ∀ W' : Set V, W'.Nonempty → IsCClosedOn (c - 1) G W' →
      (CClosedGraphs.Peeling.numMaxCliquesIn G W' : ℝ) ≤ F0 (W'.ncard : ℝ) (c - 1)) :
    ((((CClosedGraphs.Peeling.maxCliquesIn G W).filter (fun K => v ∈ K ∨ ∃ y ∈ K, G.Adj v y)).card : ℕ) : ℝ) <
      F0 (Δ : ℝ) (c - 1) * min (Δ : ℝ) ((W.ncard : ℝ) / (Δ : ℝ)) * 2 ^ c := by sorry
end CClosedGraphs.Improved
