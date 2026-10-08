-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_theorem_3
-- name    : CooperationGraphs.FairRule.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:39.323075+00:00
-- url     : https://prove2.me/theorems/39d0175c-f5bc-49e2-a8eb-0dfd931f8b91
-- title:
--   Theorem 3 — for a superadditive game the fair allocation rule is totally stable
-- statement:
--   Let $v\in\mathbb R^{CL}$ be a superadditive game in characteristic function form,
--   $$v_{S\cup T}\ge v_S+v_T\qquad\text{for all } S,T\in CL \text{ with } S\cap T=\emptyset,$$
--   and let $Y:GR\to\mathbb R^N$ be the fair allocation rule for $v$ (it satisfies the efficiency condition (7) and the equity condition (10)). Then $Y$ is totally stable:
--   $$Y_n(g)\ge Y_n(g\setminus n{:}m)\qquad\text{for every graph } g\in GR \text{ and every link } n{:}m\in g.$$
--
--   In a superadditive game, under the fair allocation rule no player ever loses by forming an additional cooperation link; in particular the complete cooperation structure is stable.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. "The fair allocation rule" is stated as "every fair allocation rule", which is faithful because Theorem 1 gives existence and uniqueness; the hypotheses are satisfiable (a local check exhibits a fair rule of a superadditive game). Superadditivity quantifies over nonempty coalitions only, as $CL$ excludes $\emptyset$; the game's value at $\emptyset$ is never read.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), Theorem 3, p. 8

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Theorem 3 (p. 8): if `v` is superadditive, then the fair allocation rule for `v` is totally
stable. -/
theorem theorem_3 {n : ℕ} (hn : 0 < n) (v : Game n) (hv : IsSuperadditive v) (Y : Rule n) (hY : IsFair v Y) :
    IsTotallyStable Y := by sorry

end CooperationGraphs.FairRule
