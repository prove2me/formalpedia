-- Prove2me | Theorems.Thm_CircStability_Main_theorem_4_1
-- name    : CircStability.Main.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T13:44:58.999822+00:00
-- url     : https://prove2.me/theorems/5f20d510-99a6-4656-8053-8808d01f78a0
-- title:
--   Theorem 4.1 — locally maximal C of length c ∈ [6, n−1], many edges and e(G[C]) > h(c+1, ⌊c/2⌋−1) give G ⊆ W_{n,⌊c/2⌋,c} or Ḡ ∈ {W_{n,k,c}, Z_{n,k,c}}
-- statement:
--   Let $k\ge2$, let $G$ be a 2-connected graph on $n$ vertices with $\delta(G)\ge k$, and let $C$ be a locally maximal cycle of $G$ of length $c\in[6,n-1]$. Suppose
--
--   $$
--   e(G)>\max\big\{f(n,k+1,c),\ f(n,\lfloor c/2\rfloor-1,c)\big\}\quad\text{and}\quad e(G[C])>h\big(c+1,\lfloor c/2\rfloor-1\big).
--   $$
--
--   Then either $G\subseteq W_{n,\lfloor c/2\rfloor,c}$, or the $C$-closure $\overline G$ of $G$ is isomorphic to $W_{n,k,c}$ or to $Z_{n,k,c}$.
--
--   Theorem 4.1 strengthens Theorem 1.13 (the same statement for a longest cycle), which is the second branch of the proof of Theorem 1.9.
--
--   **Formalization Note.** "$G\subseteq W$" is the existence of an embedding of $G$ into $W$ (Mathlib's `⊑`, a subgraph up to relabelling); "$\overline G\in\{W,Z\}$" is isomorphism, and the $Z_{n,k,c}$ alternative carries the divisibility $(k-1)\mid n-(c-k+1)$. $e(G[C])$ counts edges of $G$, not of $\overline G$. The hypothesis $k\ge2$ is the series' standing restriction (the main theorems fail at $k=1$; $Z_{n,k,c}$ divides by $k-1$).
-- source:
--   Ma and Ning, Stability results on the circumference of a graph, arXiv:1708.00704v2, p. 17, Theorem 4.1 (proof pp. 17–18)

import Mathlib
import Definitions.Def_CircStability_Main_Setting
import Definitions.Def_CircStability_Main_Closure
open Finset SimpleGraph

namespace CircStability.Main

theorem theorem_4_1 (n k c : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : TwoConnected G) (hδ : ∀ v, k ≤ G.degree v) {u : Fin n} (C : G.Walk u u)
    (hC : IsLocallyMaximal G C) (hlen : C.length = c) (hc : 6 ≤ c) (hcn : c ≤ n - 1)
    (hE : max (fNum n (k + 1) c) (fNum n (c / 2 - 1) c) < #G.edgeFinset)
    (hEC : hNum (c + 1) (c / 2 - 1) < edgesOnCycle G C.support.toFinset) :
    G ⊑ wGraph n (c / 2) c ∨
      Nonempty (cClosure G C.support.toFinset ≃g wGraph n k c) ∨
      ((k - 1) ∣ (n - (c - k + 1)) ∧ Nonempty (cClosure G C.support.toFinset ≃g zGraph n k c)) := by sorry

end CircStability.Main
