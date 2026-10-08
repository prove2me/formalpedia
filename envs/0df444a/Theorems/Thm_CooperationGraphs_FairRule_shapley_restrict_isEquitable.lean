-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_shapley_restrict_isEquitable
-- name    : CooperationGraphs.FairRule.shapley_restrict_isEquitable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:19.886112+00:00
-- url     : https://prove2.me/theorems/16979dd6-5c0a-4a1e-83f4-dd5b2f23d639
-- title:
--   Proof of Theorem 2, p. 13 — $g\mapsto\varphi(v/g)$ satisfies the equity condition (10)
-- statement:
--   Let $v\in\mathbb R^{CL}$ and let $\varphi$ be the Shapley value. For every graph $g$ on $N$ and every link $n{:}m\in g$,
--   $$\varphi_n(v/g)-\varphi_m(v/g)=\varphi_n\big(v/(g\setminus n{:}m)\big)-\varphi_m\big(v/(g\setminus n{:}m)\big),$$
--   that is, the rule $Y(g)=\varphi(v/g)$ satisfies the equity condition (10).
--
--   Together with the efficiency on components, this shows that $g\mapsto\varphi(v/g)$ is a fair allocation rule, which by the uniqueness in Theorem 1 gives Theorem 2.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. Stated as `IsEquitable (fun g => φ(v/g))`, whose unfolding is the displayed identity rearranged: $\varphi_n(v/g)-\varphi_n(v/(g\setminus n{:}m))=\varphi_m(v/g)-\varphi_m(v/(g\setminus n{:}m))$.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), proof of Theorem 2, p. 13

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Proof of Theorem 2, p. 13: the rule `g ↦ φ(v/g)` satisfies the equity condition (10):
`φ_a(v/g) − φ_b(v/g) = φ_a(v/(g \ a,b)) − φ_b(v/(g \ a,b))` for every link `a,b ∈ g`. -/
theorem shapley_restrict_isEquitable {n : ℕ} (hn : 0 < n) (v : Game n) :
    IsEquitable (fun g => shapley (restrict v g)) := by sorry

end CooperationGraphs.FairRule
