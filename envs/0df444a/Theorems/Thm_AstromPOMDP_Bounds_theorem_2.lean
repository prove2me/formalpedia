-- Prove2me | Theorems.Thm_AstromPOMDP_Bounds_theorem_2
-- name    : AstromPOMDP.Bounds.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:16:51.636088+00:00
-- url     : https://prove2.me/theorems/38d18735-4de1-40a8-9004-80bd0d82f02f
-- title:
--   Theorem 2 — a Bellman-minimizing feedback law solves P.1 and identifies its minimal value
-- statement:
--   For a finite partially observed control model satisfying the standing conditions of §II, let $V$ be the backward solution of the partial-observation equation (3.28). A feedback selector $c^0$ attaining its minimum at every probability belief exists, and for **every** such selector the resulting observation-history law $u(t)=c^0(w(t),t)$ is admissible, minimizes the pathwise expected loss (2.6) among **all** admissible observation-history laws, and has value
--   $$\mathrm{OPT}=J(c^0)=\mathbb E_{\eta_1}[V_1(w(1))].$$
--
--   This identifies the Bellman value with the original problem P.1 and is the link used in (5.12).
--
--   **Formalization Note** The printed theorem calls the law $C^0$ without defining it there; this is the minimizer $c^0$ of Theorem 1. The first output law and posterior are computed from the initial distribution of $x_1$. Impossible histories may receive any control in $U$; their posterior has no conditional-probability interpretation.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), https://doi.org/10.1016/0022-247X(65)90154-X, p. 185, Theorem 2 and (3.29)

import Definitions.Def_AstromPOMDP_Bounds_Model

namespace AstromPOMDP.Bounds

variable {St Obs : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
  [Fintype Obs] [DecidableEq Obs] [Nonempty Obs]
  {d N : ℕ} [NeZero N]

/-- Åström, *Optimal Control of Markov Processes with Incomplete State Information*,
J. Math. Anal. Appl. 10 (1965), Theorem 2, p. 185, (3.29).

The printed `C⁰` is Theorem 1's law `u(t) = c⁰(w(t), t)` with `c⁰` attaining
the minimum in (3.28); it is undefined in Theorem 2's own text. The statement
asserts that such a selector exists and that **every** selector attaining the
minimum on the simplex yields an optimal law with cost (3.29). The loss on the left is the
joint-path objective (2.6) over all admissible observation-history laws.
The first law is that of `x₁`, and a zero-probability first output contributes
zero to the finite expectation. -/
theorem theorem_2 (m : Model St Obs d N) :
    (∃ a : ℕ → Belief St → Control d,
      (∀ t, 1 ≤ t → t ≤ N → ∀ w, a t w ∈ m.U) ∧
      (∀ t, 1 ≤ t → t ≤ N → ∀ w, IsBelief w →
        V m t w = bellmanRHS m t (V m (t + 1)) w (a t w))) ∧
    (∀ a : ℕ → Belief St → Control d,
      (∀ t, 1 ≤ t → t ≤ N → ∀ w, a t w ∈ m.U) →
      (∀ t, 1 ≤ t → t ≤ N → ∀ w, IsBelief w →
        V m t w = bellmanRHS m t (V m (t + 1)) w (a t w)) →
      Admissible m (feedbackPolicy m a) ∧
      expectedCost m (feedbackPolicy m a) = firstExpectation m (V m 1) ∧
      (∀ c : Policy Obs d, Admissible m c →
        expectedCost m (feedbackPolicy m a) ≤ expectedCost m c)) ∧
    optimalCost m = firstExpectation m (V m 1) := by sorry

end AstromPOMDP.Bounds
