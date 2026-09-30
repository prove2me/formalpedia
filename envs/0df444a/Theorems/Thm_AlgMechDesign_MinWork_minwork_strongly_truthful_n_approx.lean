-- Prove2me | Theorems.Thm_AlgMechDesign_MinWork_minwork_strongly_truthful_n_approx
-- name    : AlgMechDesign.MinWork.minwork_strongly_truthful_n_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T18:29:15.707577+00:00
-- url     : https://prove2.me/theorems/5cf7bf06-0ad9-4126-b42f-4be301c482a7
-- title:
--   Theorem 4.1 — MinWork is a strongly truthful n-approximation mechanism
-- statement:
--   Consider task scheduling on unrelated machines with $n \ge 2$ agents and $k$ tasks, agent $i$ needing time $t^i_j > 0$ for task $j$. Let $x(\cdot)$ be any MinWork allocation rule (each task goes to an agent with minimal declared time, ties broken arbitrarily) and let
--   $$
--   p^i(d) = \sum_{j \in x^i(d)} \min_{i' \neq i} d^{i'}_j
--   $$
--   be the MinWork payments. Then:
--
--   1. the mechanism $(x, p)$ is **strongly truthful**: truth-telling is a dominant strategy for every agent, and every positive misreport is strictly worse than the truth for some positive declarations of the others;
--   2. $x$ is an **$n$-approximation**: for every positive type vector $t$ and every allocation $y$, $\; g(x(t), t) \le n \cdot g(y, t)$, where $g$ is the make-span.
--
--   This is the upper bound of the paper's task scheduling section; the paper's lower bounds (Theorems 4.6, 4.10, 4.12) compare against it.
--
--   **Formalization Note** The statement quantifies over every allocation rule satisfying the MinWork specification, so it holds for every tie-breaking rule. The hypothesis $n \ge 2$ makes the second-best minimum $\min_{i'\neq i}$ well defined; `[NeZero n]` is implied by it and only makes the make-span's maximum typecheck. Running time ("polynomial time") is not modelled.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 176, Theorem 4.1

import Mathlib
import Definitions.Def_AlgMechDesign_MinWork_Model
import Definitions.Def_AlgMechDesign_MinWork_Mechanism

namespace AlgMechDesign.MinWork

/-- Theorem 4.1: for `n ≥ 2` agents, any number `k` of tasks and every tie-breaking rule, the
MinWork mechanism is strongly truthful and an `n`-approximation for task scheduling. -/
theorem minwork_strongly_truthful_n_approx {n k : ℕ} [NeZero n] (hn : 2 ≤ n)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n)) (hmin : IsMinWorkAlloc alloc) :
    IsStronglyTruthful alloc (minWorkPay hn alloc) ∧ IsApprox (n : ℝ) alloc := by sorry

end AlgMechDesign.MinWork
