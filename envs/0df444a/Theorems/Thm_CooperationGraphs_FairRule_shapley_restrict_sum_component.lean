-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_shapley_restrict_sum_component
-- name    : CooperationGraphs.FairRule.shapley_restrict_sum_component
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:29.917378+00:00
-- url     : https://prove2.me/theorems/117dcb5d-600a-476c-a912-e3084f01a0f9
-- title:
--   Proof of Theorem 2, p. 13 — $\sum_{n\in S}\varphi_n(v/g)=\sum_{R\in S/g}v_R$ on components
-- statement:
--   Let $v\in\mathbb R^{CL}$, let $g$ be a graph on $N$ and let $\varphi$ be the Shapley value. For every connected component $S\in N/g$,
--   $$\sum_{n\in S}\varphi_n(v/g)=\sum_{R\in S/g}v_R .$$
--
--   Since $S/g=\{S\}$ for a component $S$ of $g$, the right-hand side is $v_S$, so the rule $g\mapsto\varphi(v/g)$ satisfies the efficiency condition (7).
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. $\varphi$ is the platform's `Supermodularity.Cooperative.ShapleyValue` applied to $v/g$ with its value at $\emptyset$ set to $0$; $(v/g)_\emptyset=0$ already, since $\emptyset/g$ is empty.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 2, p. 13

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 2, p. 13: for every graph `g` and component `S ∈ N/g`,
`∑_{i ∈ S} φ_i(v/g) = ∑_{R ∈ S/g} v_R`. -/
theorem shapley_restrict_sum_component {n : ℕ} (hn : 0 < n) (v : Game n) (g : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (hS : S ∈ quot univ g) :
    ∑ i ∈ S, shapley (restrict v g) i = ∑ R ∈ quot S g, v R := by sorry

end CooperationGraphs.FairRule
