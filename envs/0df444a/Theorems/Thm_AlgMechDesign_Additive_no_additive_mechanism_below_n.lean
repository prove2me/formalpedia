-- Prove2me | Theorems.Thm_AlgMechDesign_Additive_no_additive_mechanism_below_n
-- name    : AlgMechDesign.Additive.no_additive_mechanism_below_n
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T19:28:38.437723+00:00
-- url     : https://prove2.me/theorems/3c731ce9-d1cd-4b2a-9059-929555387726
-- title:
--   Theorem 4.10 — no truthful additive mechanism is a $c$-approximation for task scheduling for any $c<n$
-- statement:
--   Consider task scheduling with $n\ge 1$ agents and $k \ge n^2$ tasks. Let $m=(x,p)$ be a truthful direct mechanism whose prices are additive: $p^i(X,t^{-i}) = \sum_{j\in X} p^i(\{j\},t^{-i})$ for every agent $i$, positive type vector $t$ and set of tasks $X$. Then for every real $c < n$ the allocation rule is **not** a $c$-approximation: there are a positive type vector $t$ and an allocation $y$ with
--
--   $$g\bigl(x(t),t\bigr) > c\cdot g(y,t).$$
--
--   By the revelation principle the same holds for every mechanism whose truthful implementation is additive. The bound is tight: the MinWork mechanism, which gives each task to the fastest agent and pays it the second-best time, is truthful, additive and an $n$-approximation.
--
--   **Formalization Note** The threshold $k\ge n^2$ is the one the paper's proof uses ("Let $k \ge n^2$"); the theorem's printed statement does not mention $k$. The statement is kept for every $n\ge 1$ (`[NeZero n]`); at $n=1$ it holds because every allocation is the same. Truthfulness and additivity quantify over positive types; running time is not modelled.
-- source:
--   Nisan, Ronen, Algorithmic Mechanism Design, Games Econ. Behav. 35, 2001, p. 180, Theorem 4.10

import Mathlib
import Definitions.Def_AlgMechDesign_Additive_Model
import Definitions.Def_AlgMechDesign_Additive_Price

namespace AlgMechDesign.Additive

/-- Theorem 4.10, p. 180: for `n ≥ 1` agents and `k ≥ n²` tasks, no truthful additive mechanism
for task scheduling is a `c`-approximation for any `c < n`. -/
theorem no_additive_mechanism_below_n {n k : ℕ} [NeZero n] (hk : n ^ 2 ≤ k)
    (alloc : (Fin n → Fin k → ℝ) → (Fin k → Fin n))
    (pay : (Fin n → Fin k → ℝ) → Fin n → ℝ) (htr : IsTruthful alloc pay)
    (hadd : IsAdditive alloc pay) (c : ℝ) (hc : c < n) :
    ¬ IsApprox c alloc := by sorry

end AlgMechDesign.Additive
