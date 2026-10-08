-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_carrier_identity
-- name    : CooperationGraphs.FairRule.carrier_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:10.590982+00:00
-- url     : https://prove2.me/theorems/475e1694-6046-47dc-8e4e-94e0a5ac2420
-- title:
--   Proof of Theorem 2, pp. 12–13 — $\sum_{n\in S}\varphi_n(u^T)$ is $u^T_N$ if $S=T$ and $0$ if $S\cap T=\emptyset$
-- statement:
--   Let $v\in\mathbb R^{CL}$ and let $g$ be a graph on $N$. For a component $T\in N/g$ define the game $u^T\in\mathbb R^{CL}$ by
--   $$u^T_{T'}=\sum_{R\in(T'\cap T)/g}v_R\qquad(T'\in CL).$$
--   Let $\varphi$ be the Shapley value. Then for any components $S,T\in N/g$,
--   $$\sum_{n\in S}\varphi_n(u^T)=\begin{cases}u^T_N,& S=T,\\ 0,& S\cap T=\emptyset.\end{cases}$$
--
--   The set $T$ is a carrier of $u^T$; this identity is the carrier axiom of Shapley (1953) applied to $u^T$, and with $v/g=\sum_{T\in N/g}u^T$ it gives the efficiency of $\varphi(v/g)$ on components.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. Two components of $g$ are either equal or disjoint, so the two cases are stated as `if S = T then u^T_N else 0`. $\varphi$ is the platform's `Supermodularity.Cooperative.ShapleyValue` applied to $u^T$ with its value at $\emptyset$ set to $0$ ($u^T_\emptyset=0$ in any case).
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 2, pp. 12–13, display at the top of p. 13

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 2, pp. 12–13 (carrier axiom): for `S, T ∈ N/g`,
`∑_{i ∈ S} φ_i(u^T) = u^T_N` if `S = T`, and `= 0` if `S ∩ T = ∅` (distinct components are
disjoint). -/
theorem carrier_identity {n : ℕ} (hn : 0 < n) (v : Game n) (g : SimpleGraph (Fin n))
    (S T : Finset (Fin n)) (hS : S ∈ quot univ g) (hT : T ∈ quot univ g) :
    ∑ i ∈ S, shapley (uGame v g T) i = if S = T then uGame v g T univ else 0 := by sorry

end CooperationGraphs.FairRule
