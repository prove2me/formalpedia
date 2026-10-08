-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_theorem_1
-- name    : CooperationGraphs.FairRule.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:18.208052+00:00
-- url     : https://prove2.me/theorems/7f8cccf8-b251-4ea2-be06-9f1376445f02
-- title:
--   Theorem 1 — every characteristic function game has a unique fair allocation rule
-- statement:
--   Let $N$ be a finite set of players and $v\in\mathbb R^{CL}$ a game in characteristic function form. There is a unique function $Y:GR\to\mathbb R^N$ satisfying the efficiency condition
--   $$\sum_{n\in S}Y_n(g)=v_S\qquad\text{for all } g\in GR,\ S\in N/g,\tag{7}$$
--   and the equity condition
--   $$Y_n(g)-Y_n(g\setminus n{:}m)=Y_m(g)-Y_m(g\setminus n{:}m)\qquad\text{for all } g\in GR,\ n{:}m\in g.\tag{10}$$
--
--   This is the paper's main result: the requirement that every connected group of cooperating players divides exactly its own worth, and that the two endpoints of any link gain equally from it, pins down a single allocation for every cooperation structure.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. Graphs are `SimpleGraph (Fin n)`; a game is a function on `Finset (Fin n)` whose value at $\emptyset$ is never read. The paper's $N$ is nonempty; for $N=\emptyset$ the statement holds trivially, so no nonemptiness hypothesis is needed.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), Theorem 1, p. 7

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Theorem 1 (p. 7): every characteristic function game `v` has a unique fair allocation rule,
i.e. a unique `Y : GR → ℝ^N` satisfying (7) and (10). -/
theorem theorem_1 {n : ℕ} (hn : 0 < n) (v : Game n) : ∃! Y : Rule n, IsFair v Y := by sorry

end CooperationGraphs.FairRule
