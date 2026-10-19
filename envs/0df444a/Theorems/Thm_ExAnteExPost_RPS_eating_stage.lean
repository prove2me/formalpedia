-- Prove2me | Theorems.Thm_ExAnteExPost_RPS_eating_stage
-- name    : ExAnteExPost.RPS.eating_stage
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:41.534981+00:00
-- url     : https://prove2.me/theorems/f394f1e5-132e-402b-9d20-9b67e5b57101
-- title:
--   §3.1, p. 9 — one unit of eating satisfies Theorem 1's hypotheses and gives every agent mass one
-- statement:
--   Fix an instance and a favorite-good choice rule, and let $M' \subseteq M$. Let $X = \mathrm{Eating}(M', 1)$ be the partial fractional allocation produced by running the eating protocol on $M'$ for one unit of time. Then
--
--   1. $X$ satisfies the hypotheses of Theorem 1: every entry lies in $[0,1]$ and every row and column sum is at most $1$;
--   2. $X_{i,g} = 0$ for every agent $i$ and every good $g \notin M'$;
--   3. if $|M'| \ge n$, every agent has consumed a total mass of exactly one item:
--   $$\sum_{g} X_{i,g} = 1 \quad \text{for every agent } i .$$
--
--   This is the statement "after one unit of time every agent has consumed a total mass of one item" on which the decomposition step of Algorithm 1 rests: it lets Theorem 1 be applied to $X$, and with conclusion (3a) it forces exactly one good per agent in each stage before the last.
--
--   **Formalization Note.** The page states the mass-one property for the stages of Algorithm 1, where at least $n$ goods remain; the hypothesis $|M'| \ge n$ makes that explicit (with fewer goods than agents, all goods are exhausted before time one).
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, p. 9, §3.1

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

namespace ExAnteExPost.RPS
open Finset

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- §3.1, p. 9: one unit of eating on `M'` gives a matrix satisfying the hypotheses of
Theorem 1, supported on `M'`, in which every agent has eaten a total mass of one when there are at
least as many goods in `M'` as agents. -/
theorem eating_stage [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (M' : Finset G) :
    BvNInput (eating pick M') ∧ (∀ i g, g ∉ M' → eating pick M' i g = 0) ∧
      (Fintype.card N ≤ M'.card → ∀ i, ∑ g, eating pick M' i g = 1) := by sorry
end ExAnteExPost.RPS
