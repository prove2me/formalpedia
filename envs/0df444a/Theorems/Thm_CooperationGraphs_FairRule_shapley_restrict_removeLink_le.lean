-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_shapley_restrict_removeLink_le
-- name    : CooperationGraphs.FairRule.shapley_restrict_removeLink_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:34.835706+00:00
-- url     : https://prove2.me/theorems/288c95f8-a2ba-475f-87e8-4891dd01fe5f
-- title:
--   Proof of Theorem 3, p. 13 — for superadditive $v$, $\varphi_n(v/g)-\varphi_n(v/g\setminus n{:}m)\ge0$
-- statement:
--   Let $v\in\mathbb R^{CL}$ be superadditive, let $\varphi$ be the Shapley value, let $g$ be a graph on $N$ and $n{:}m$ a link of $g$. Then
--   $$\varphi_n(v/g)-\varphi_n\big(v/(g\setminus n{:}m)\big)\ge 0 .$$
--
--   With Theorem 2 this is exactly total stability of the fair allocation rule: a player never loses by keeping a link.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. $\varphi$ is the platform's `Supermodularity.Cooperative.ShapleyValue` applied after setting the game's value at $\emptyset$ to $0$. The link condition comes from the paper's context.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 3 (headed "PROOF OF THEOREM 4." in the typescript), p. 13

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 3, p. 13: if `v` is superadditive then `φ_a(v/g) − φ_a(v/(g \ a,b)) ≥ 0`. -/
theorem shapley_restrict_removeLink_le {n : ℕ} (hn : 0 < n) (v : Game n) (hv : IsSuperadditive v)
    (g : SimpleGraph (Fin n)) (a b : Fin n) (hab : g.Adj a b) :
    shapley (restrict v (removeLink g a b)) a ≤ shapley (restrict v g) a := by sorry

end CooperationGraphs.FairRule
