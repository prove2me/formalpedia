-- Prove2me | Theorems.Thm_ContractUnobs_Compare_equation_2
-- name    : ContractUnobs.Compare.equation_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T22:17:52.935431+00:00
-- url     : https://prove2.me/theorems/70b471b7-f876-4c6c-bad4-94cbcb120835
-- title:
--   Equation (2), p. 13 — retailer best response under a conjectured rival price: p = (1+θp̃)/(2+2θ) + w/2, Q = demand
-- statement:
--   Fix the competition parameter $\theta \ge 0$, a retailer's belief $\tilde p \ge 0$ about its rival's price, and a contract $(K, w)$ with $w \ge 0$ and
--   $$(1+\theta)\,w < 1 + \theta \tilde p .$$
--   Among admissible accepting actions $(p, Q)$ (with $p, Q \ge 0$), an action maximizes the conjectured profit $\tilde\pi = p\min(Q, \max(0, 1 - p + \theta(\tilde p - p))) - wQ - K$ if and only if
--   $$p = \frac{1 + \theta \tilde p}{2 + 2\theta} + \frac{w}{2}$$
--   and $Q = 1 - p + \theta(\tilde p - p)$, except that when $w = 0$ any $Q \ge 1 - p + \theta(\tilde p - p)$ is also optimal. The maximal conjectured profit over accepting actions is
--   $$\frac{\bigl(1 + \theta\tilde p - (1+\theta) w\bigr)^2}{4(1+\theta)} - K .$$
--
--   This is the retailer's best response under passive beliefs, the building block of both equilibria: the price does not depend on the rival's wholesale price, which the retailer cannot see.
--
--   **Formalization Note** The page's side condition "if $w_i \le \tilde p_j$" is replaced by the exact condition $(1+\theta)w < 1 + \theta\tilde p$ under which the optimal order is positive (it follows from $w \le \tilde p < 1$). The non-uniqueness of $Q$ at $w = 0$ is stated explicitly, since at zero marginal cost any order covering demand is optimal. The maximal value is not printed on the page; it is the value at the displayed solution.
-- source:
--   Li & Liu, Contract Unobservability and Downstream Competition, SSRN 3339702, p. 13, Equation (2) (and p. 14, first line, "if w_i ≤ p̃_j")

import Mathlib
import Definitions.Def_ContractUnobs_Compare_Model

namespace ContractUnobs.Compare

theorem equation_2 (θ pt : ℝ) (hθ : 0 ≤ θ) (hpt : 0 ≤ pt) (C : Contract) (hw : 0 ≤ C.w)
    (hint : (1 + θ) * C.w < 1 + θ * pt) :
    (∀ a : Action, a.Feasible → a.accept = true →
      ((∀ b : Action, b.Feasible → b.accept = true → conjProfit θ pt C b ≤ conjProfit θ pt C a) ↔
        (a.p = (1 + θ * pt) / (2 + 2 * θ) + C.w / 2 ∧
          (a.Q = demand θ a.p pt ∨ (C.w = 0 ∧ demand θ a.p pt ≤ a.Q))))) ∧
    IsGreatest (conjProfit θ pt C '' {b : Action | b.Feasible ∧ b.accept = true})
      ((1 + θ * pt - (1 + θ) * C.w) ^ 2 / (4 * (1 + θ)) - C.K) := by sorry

end ContractUnobs.Compare
