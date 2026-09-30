-- Prove2me | Theorems.Thm_AlgMechDesign_NonOptimal_comp_bonus_nonoptimal_not_truthful
-- name    : AlgMechDesign.NonOptimal.comp_bonus_nonoptimal_not_truthful
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T21:53:05.036569+00:00
-- url     : https://prove2.me/theorems/8664e2fe-626c-44a6-b317-2c0b02df6fb7
-- title:
--   Theorem 5.6 — the Compensation-and-Bonus mechanism based on a non-optimal approximation algorithm is not truthful
-- statement:
--   Consider task scheduling with verification with $n \ge 1$ agents and $k$ tasks. Let $x(\cdot)$ be an allocation algorithm, mapping every declared type vector to an allocation, and suppose that
--
--   1. $x(\cdot)$ is an **approximation algorithm**: there is a real constant $c$ such that for every positive type vector $t$ and every allocation $y$,
--   $$g\bigl(x(t),t\bigr) \le c\, g(y,t);$$
--   2. $x(\cdot)$ is **not optimal**: there are a positive type vector $t$ and an allocation $y$ with $g(y,t) < g\bigl(x(t),t\bigr)$.
--
--   Then the Compensation-and-Bonus mechanism based on $x(\cdot)$ — the mechanism of Definition 24 with the optimal algorithm replaced by $x(\cdot)$ — is **not truthful**: there are an agent $i$ and a positive type $t^i$ such that no strategy of the form (declare $t^i$, execute according to some feasible plan) is dominant.
--
--   Together with Theorem 5.1 (the Compensation-and-Bonus mechanism with an optimal algorithm is strongly truthful), this shows that the truthfulness of that mechanism rests on exact optimization: it cannot be combined with an arbitrary approximation algorithm, which motivates the separate rounding-based mechanism for bounded scheduling.
--
--   **Formalization Note** "Approximation algorithm" is encoded as a finite approximation ratio $c$ (existentially quantified, not fixed); "non-optimal" as the existence of one positive type vector on which the algorithm's make-span is not the minimum. The number of agents is at least one (`[NeZero n]`); with no agents there is no allocation algorithm meeting the hypotheses. Truthfulness is Definition 19 for mechanisms with verification: dominance is tested against all positive declarations and all execution plans of the other agents, and against all positive declarations and feasible execution plans of the agent itself. Running time is not modelled.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 191, Theorem 5.6 (with Definition 32); proof on p. 192

import Mathlib
import Definitions.Def_AlgMechDesign_NonOptimal_Model

open Finset

namespace AlgMechDesign.NonOptimal

/-- Theorem 5.6 (Nisan–Ronen, p. 191). Let `alloc` be an approximation algorithm for task
scheduling (make-span within some finite factor `c` of every allocation, on every positive type
vector) that is not optimal (on some positive type vector some allocation has strictly smaller
make-span than the one `alloc` chooses). Then the Compensation-and-Bonus mechanism based on
`alloc` is not truthful. -/
theorem comp_bonus_nonoptimal_not_truthful {n k : ℕ} [NeZero n]
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (happrox : ∃ c : ℝ, ∀ t : Fin n → Fin k → ℝ, IsType t → ∀ y : Fin k → Fin n,
      makespan t (alloc t) ≤ c * makespan t y)
    (hnonopt : ∃ t : Fin n → Fin k → ℝ, IsType t ∧ ∃ y : Fin k → Fin n,
      makespan t y < makespan t (alloc t)) :
    ¬ Truthful alloc := by sorry

end AlgMechDesign.NonOptimal
