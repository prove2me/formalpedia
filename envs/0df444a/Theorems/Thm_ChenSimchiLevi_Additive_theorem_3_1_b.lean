-- Prove2me | Theorems.Thm_ChenSimchiLevi_Additive_theorem_3_1_b
-- name    : ChenSimchiLevi.Additive.theorem_3_1_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:42:09.207874+00:00
-- url     : https://prove2.me/theorems/7c417cfa-405b-400b-8cd9-c1596b13f423
-- title:
--   Theorem 3.1(b) — $g_t$ is continuous, $g_t(y,d) \to -\infty$ as $|y| \to \infty$, and a best expected demand exists
-- statement:
--   Consider the model of Chen and Simchi-Levi (2004) under Assumptions 1–5 (with $c_{T+1} = 0$, $c_t \ge 0$, $k \ge 0$) and additive demand. For every period $t = T, T-1, \dots, 1$:
--
--   1. $g_t(y, d)$ is continuous in $(y, d)$ on $\mathbb R \times [\underline d_t, \bar d_t]$;
--   2. for every $d \in [\underline d_t, \bar d_t]$,
--   $$\lim_{|y| \to \infty} g_t(y, d) = -\infty;$$
--   3. for every fixed $y$, $g_t(y, \cdot)$ attains its maximum over $[\underline d_t, \bar d_t]$ at some point, denoted $d_t(y)$.
--
--   Here $g_t$ is the one-period objective (3) with continuation $v_{t+1}$. Part 3 makes $g_t(y, d_t(y))$, the quantity whose $k$-concavity is the heart of Theorem 3.1, a well-defined maximum; part 2 makes it coercive, so that an order-up-to level exists.
--
--   **Formalization Note.** The proof of part 2 in the paper uses $c_{t+1} \ge 0$; this is why the model's assumptions include $c_t \ge 0$ and $c_{T+1} = 0$.
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), p. 890, Theorem 3.1(b)

import Mathlib
import Definitions.Def_ChenSimchiLevi_Additive_Model

open Filter

namespace ChenSimchiLevi.Additive

/-- Theorem 3.1(b) of Chen–Simchi-Levi (2004), p. 890: for `t = T, T - 1, …, 1`, `g_t(y, d)` is
continuous in `(y, d)`, `lim_{|y| → ∞} g_t(y, d) = -∞` for every `d ∈ [d_t, d̄_t]`, and for every
`y` the function `g_t(y, ·)` attains its maximum on `[d_t, d̄_t]`. -/
theorem theorem_3_1_b (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive) :
    ∀ t ∈ Finset.Icc 1 M.T,
      ContinuousOn (Function.uncurry (M.g t)) (Set.univ ×ˢ Set.Icc (M.dlo t) (M.dhi t)) ∧
      (∀ d ∈ Set.Icc (M.dlo t) (M.dhi t), Tendsto (fun y => M.g t y d) (cocompact ℝ) atBot) ∧
      (∀ y : ℝ, ∃ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        IsMaxOn (M.g t y) (Set.Icc (M.dlo t) (M.dhi t)) d) := by sorry

end ChenSimchiLevi.Additive
