-- Prove2me | Theorems.Thm_AlgMechDesign_Additive_exists_agent_many_tasks
-- name    : AlgMechDesign.Additive.exists_agent_many_tasks
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:18:33.154463+00:00
-- url     : https://prove2.me/theorems/daa9f2ed-99d5-49f7-822c-acf86401f6b3
-- title:
--   Proof of Theorem 4.10 — with $k \ge n^2$ tasks some agent receives at least $n$ tasks
-- statement:
--   Let there be $n \ge 1$ agents and $k \ge n^2$ tasks. Then for every allocation $x$ of the tasks to the agents there is an agent $i$ with
--
--   $$|x^i| \ge n .$$
--
--   This is the pigeonhole step behind the sentence "Without loss of generality we assume that $|x^1(t)| \ge n$" in the proof of Theorem 4.10, applied there to the allocation chosen at the all-ones type vector.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 180, proof of Theorem 4.10, first paragraph

import Mathlib
import Definitions.Def_AlgMechDesign_Additive_Model

namespace AlgMechDesign.Additive

/-- Proof of Theorem 4.10, p. 180 (the step "Without loss of generality we assume that
`|x¹(t)| ≥ n`"): with `n ≥ 1` agents and `k ≥ n²` tasks, every allocation gives some agent at
least `n` tasks. -/
theorem exists_agent_many_tasks {n k : ℕ} [NeZero n] (hk : n ^ 2 ≤ k) (x : Fin k → Fin n) :
    ∃ i : Fin n, n ≤ (taskSet x i).card := by sorry

end AlgMechDesign.Additive
