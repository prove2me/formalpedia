-- Prove2me | Theorems.Thm_AlgMechDesign_Randomized_rbmw_approx
-- name    : AlgMechDesign.Randomized.rbmw_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T20:48:33.378983+00:00
-- url     : https://prove2.me/theorems/0655a2b6-8a3f-4a54-a181-3aba3a425f09
-- title:
--   Lemma 4.18 — the randomly biased min work mechanism is a 7/4-approximation
-- statement:
--   Consider task scheduling with two agents and $k$ tasks. For every positive type vector $t$ and every allocation $y$ of the tasks,
--   $$
--   \frac{1}{2^k}\sum_{s \in \{1,2\}^k} g\big(x_s(t), t\big) \le \frac74\, g(y, t),
--   $$
--   where $x_s$ is the allocation of the biased min work mechanism with $\beta = 4/3$ and bit vector $s$, and $g$ is the make-span. In words: the expected make-span of the randomly biased min work mechanism is at most $7/4$ times the optimal make-span.
--
--   Together with Lemma 4.17 this gives Theorem 4.16.
--
--   **Formalization Note** The objective of a randomized mechanism is the expectation of the make-span (Definition 15), here a uniform average over all $2^k$ vectors $s$; comparing with every allocation $y$ is comparing with the optimum.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 182, Lemma 4.18 (proof pp. 183–185)

import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model
import Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork

namespace AlgMechDesign.Randomized

/-- Lemma 4.18: for every number `k` of tasks, every positive type vector `t` of the two agents
and every allocation `y`, the expected make-span of the randomly biased min work mechanism is at
most `7/4` times the make-span of `y`. -/
theorem rbmw_approx {k : ℕ} (t : Fin 2 → Fin k → ℝ) (ht : IsType t) (y : Fin k → Fin 2) :
    expMakespan t ≤ 7 / 4 * makespan t y := by sorry

end AlgMechDesign.Randomized
