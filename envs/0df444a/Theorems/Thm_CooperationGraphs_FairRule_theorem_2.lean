-- Prove2me | Theorems.Thm_CooperationGraphs_FairRule_theorem_2
-- name    : CooperationGraphs.FairRule.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:29.489404+00:00
-- url     : https://prove2.me/theorems/b2620a6b-3c0c-4649-b17a-88e50dbea8ef
-- title:
--   Theorem 2 — the fair allocation rule is $Y(g)=\varphi(v/g)$, the Shapley value of the graph-restricted game
-- statement:
--   Let $v\in\mathbb R^{CL}$ be a game in characteristic function form and let $Y:GR\to\mathbb R^N$ be the fair allocation rule for $v$, i.e. $Y$ satisfies the efficiency condition (7) and the equity condition (10). Then
--   $$Y(g)=\varphi(v/g)\qquad\text{for all } g\in GR,$$
--   where $\varphi:\mathbb R^{CL}\to\mathbb R^N$ is the Shapley value operator and $(v/g)_S=\sum_{T\in S/g}v_T$ is the graph-restricted game. In particular, $Y(\bar g^N)=\varphi(v)$.
--
--   The fair allocation rule is therefore computed by an explicit formula (later called the Myerson value), and at the complete graph it reduces to the Shapley value.
--
--   **Formalization Note.** The paper assumes a nonempty player set, stated as $0<n$. "The unique fair allocation rule" is stated as "every fair allocation rule"; existence and uniqueness are Theorem 1. $\varphi$ is the platform's `Supermodularity.Cooperative.ShapleyValue` applied after setting the game's value at $\emptyset$ to $0$. $\bar g^N$ is the complete graph `⊤`.
-- source:
--   Myerson, Graphs and Cooperation in Games, Discussion Paper No. 246 (Sept. 1976), Theorem 2, p. 8

import Mathlib
import Definitions.Def_CooperationGraphs_FairRule_Basic

namespace CooperationGraphs.FairRule

open Finset
open scoped Classical

/-- Theorem 2 (p. 8): the fair allocation rule `Y` for `v` satisfies `Y(g) = φ(v/g)` for every
graph `g`; in particular `Y(ḡ^N) = φ(v)`. -/
theorem theorem_2 {n : ℕ} (hn : 0 < n) (v : Game n) (Y : Rule n) (hY : IsFair v Y) :
    (∀ g : SimpleGraph (Fin n), Y g = shapley (restrict v g)) ∧ Y ⊤ = shapley v := by sorry

end CooperationGraphs.FairRule
