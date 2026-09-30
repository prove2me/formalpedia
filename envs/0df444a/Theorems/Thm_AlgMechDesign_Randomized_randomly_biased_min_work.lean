-- Prove2me | Theorems.Thm_AlgMechDesign_Randomized_randomly_biased_min_work
-- name    : AlgMechDesign.Randomized.randomly_biased_min_work
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T20:51:57.42828+00:00
-- url     : https://prove2.me/theorems/7036a0d1-cd24-46b9-ab22-8e4b53a67353
-- title:
--   Theorem 4.16 — the randomly biased min work mechanism is a strongly truthful 7/4-approximation for two agents
-- statement:
--   Consider task scheduling with two agents and any number $k$ of tasks. The randomly biased min work mechanism, the uniform distribution over the biased min work mechanisms with $\beta = 4/3$ and $s \in \{1,2\}^k$, has both of the following properties.
--
--   1. It is universally strongly truthful: each biased min work mechanism with $\beta = 4/3$ is truthful on positive types, and every positive misreport $d^i \ne t^i$ is strictly worse than the truth for some $s$ and some positive declaration of the other agent.
--   2. It is a $7/4$-approximation in expectation: for every positive type vector $t$ and every allocation $y$,
--   $$
--   \frac{1}{2^k}\sum_{s \in \{1,2\}^k} g\big(x_s(t), t\big) \le \frac74\, g(y, t).
--   $$
--
--   No deterministic mechanism achieves a ratio below $2$ for two agents (Theorem 4.6 of the same paper), so randomization strictly helps.
--
--   **Formalization Note** "(Polynomial time computable)" is not formalized: running time is out of scope. The objective of a randomized mechanism is its expected make-span (Definition 15), a uniform average over all $2^k$ bit vectors. Truthfulness is universal (for every $s$), not in expectation.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 182, Theorem 4.16

import Mathlib
import Definitions.Def_AlgMechDesign_Randomized_Model
import Definitions.Def_AlgMechDesign_Randomized_BiasedMinWork

namespace AlgMechDesign.Randomized

/-- Theorem 4.16: for every number `k` of tasks, the randomly biased min work mechanism is a
universally strongly truthful implementation of a `7/4`-approximation (in expected make-span)
for task scheduling with two agents. -/
theorem randomly_biased_min_work {k : ℕ} :
    IsUniversallyStronglyTruthful (n := 2) (k := k) (R := Fin k → Fin 2) rbmwAlloc rbmwPay ∧
      ∀ t : Fin 2 → Fin k → ℝ, IsType t → ∀ y : Fin k → Fin 2,
        expMakespan t ≤ 7 / 4 * makespan t y := by sorry

end AlgMechDesign.Randomized
