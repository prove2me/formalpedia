-- Prove2me | Theorems.Thm_ChenSimchiLevi_Additive_theorem_3_1_a
-- name    : ChenSimchiLevi.Additive.theorem_3_1_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:41:44.963492+00:00
-- url     : https://prove2.me/theorems/c2754e30-263a-4615-9033-a057abde80ba
-- title:
--   Theorem 3.1(a) — $g_t(y,d) = O(|y|^\rho)$ and $v_t(x) = O(|x|^\rho)$
-- statement:
--   Consider the model of Chen and Simchi-Levi (2004) under Assumptions 1–5 (with $c_{T+1} = 0$, $c_t \ge 0$, $k \ge 0$) and additive demand. For every period $t = T, T-1, \dots, 1$:
--
--   1. the expectation $\mathbb E\, v_{t+1}(y - d - \beta_t)$ in (3) is finite for every $y$ and every $d \in [\underline d_t, \bar d_t]$;
--   2. there is a constant $C$ with
--   $$|g_t(y, d)| \le C\,(1 + |y|^\rho) \quad\text{for all } y \in \mathbb R,\ d \in [\underline d_t, \bar d_t];$$
--   3. there is a constant $C'$ with $|v_t(x)| \le C'(1 + |x|^\rho)$ for all $x \in \mathbb R$.
--
--   Here $g_t$ is the one-period objective (3) and $v_t$ the profit-to-go (2). The growth bounds keep the expectations in the dynamic program finite from one period to the next.
--
--   **Formalization Note.** The paper's $O(|y|^\rho)$ is written as an explicit bound $C(1 + |y|^\rho)$, with the constant uniform in $d$. Item 1 is added: it states the finiteness of the expectation in (3), which the paper presupposes (in Lean a non-integrable function has integral $0$).
-- source:
--   Chen, Simchi-Levi, Coordinating Inventory Control and Pricing Strategies with Random Demand and Fixed Ordering Cost: The Finite Horizon Case, Operations Research 52(6) (2004), p. 890, Theorem 3.1(a)

import Mathlib
import Definitions.Def_ChenSimchiLevi_Additive_Model

open MeasureTheory

namespace ChenSimchiLevi.Additive

/-- Theorem 3.1(a) of Chen–Simchi-Levi (2004), p. 890: for `t = T, T - 1, …, 1`, the expectation
of `v_{t+1}` in (3) is finite, `g_t(y, d) = O(|y|^ρ)` (uniformly in `d ∈ [d_t, d̄_t]`) and
`v_t(x) = O(|x|^ρ)`. -/
theorem theorem_3_1_a (M : Model) (hA : M.Assumptions) (hadd : M.IsAdditive) :
    ∀ t ∈ Finset.Icc 1 M.T,
      (∀ y : ℝ, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        Integrable (fun ε : ℝ × ℝ => M.v (t + 1) (y - (ε.1 * d + ε.2))) (M.μ t)) ∧
      (∃ C : ℝ, ∀ y : ℝ, ∀ d ∈ Set.Icc (M.dlo t) (M.dhi t),
        |M.g t y d| ≤ C * (1 + |y| ^ M.ρ)) ∧
      (∃ C : ℝ, ∀ x : ℝ, |M.v t x| ≤ C * (1 + |x| ^ M.ρ)) := by sorry

end ChenSimchiLevi.Additive
