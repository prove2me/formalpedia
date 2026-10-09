-- Prove2me | Theorems.Thm_AstromPOMDP_Reduction_theorem_3
-- name    : AstromPOMDP.Reduction.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T11:08:22.147224+00:00
-- url     : https://prove2.me/theorems/625ec129-d566-42b1-83e4-49d2acc696d3
-- title:
--   Theorem 3, p. 188 — P.1 and P.2 are equivalent, with the optimal law u(t) = c⁰(w(t), t) in both
-- statement:
--   Consider Åström's controlled finite Markov chain with incomplete state information, problem P.1 (minimize the expected cost (2.6) over admissible control laws of the observed outputs $\eta_1,\dots,\eta_t$) and problem P.2 (minimize the functional (4.4) of the process $w(t)$ of conditional state distributions over admissible laws of the history $w(1),\dots,w(t)$).
--
--   1. P.1 has a solution if and only if P.2 has a solution.
--   2. Let $(V,c^0)$ solve the functional equation (3.28),
--   $$
--   V_k(w)=\min_{u\in U}\Big\{\sum_i g(u,i,k)\,w_i+\sum_j V_{k+1}\Big(\frac{z^j(u,w)}{\|z^j(u,w)\|}\Big)\|z^j(u,w)\|\Big\},\qquad V_{N+1}=0,
--   $$
--   with $c^0(w,k)\in U$ attaining the minimum. Then the law
--   $$
--   u(t)=c^0(w(t),t)
--   $$
--   is optimal for P.1 (with $w(t)$ computed from the outputs by (3.25) under this law) and for P.2, among all admissible laws of each problem, and both minimal values equal $E_{\eta_1}V_1(w(1))=\sum_j P(y_1=j)\,V_1(w(1)\mid\eta_1=j)$.
--
--   The theorem transforms optimal control with incomplete state information into optimal control with complete state information, the state being the conditional distribution of the hidden state. It generalizes the separation theorem for linear systems with quadratic cost.
--
--   **Formalization Note** "$c^0$ is given by Theorem 1" is read as: $c^0$ attains the minimum in (3.28). On the probability simplex the solution of (3.28) with $V_{N+1}=0$ is unique and equals the cost-to-go of Theorem 1. Part 2 is the substance of the theorem; part 1 alone would hold trivially in a setting where both problems always have solutions.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), DOI 10.1016/0022-247X(65)90154-X, p. 188, Theorem 3; problems P.1 (p. 179) and P.2 (p. 188)

import Mathlib
import Definitions.Def_AstromPOMDP_Reduction_BeliefProcess

namespace AstromPOMDP.Reduction

/-- Åström (1965), J. Math. Anal. Appl. 10:174–205, Theorem 3, p. 188: the problems P.1 and P.2
are equivalent in the sense that if one of them has a solution then so has the other, and the
optimal control law is `u(t) = c⁰(w(t), t)` in both cases, where `c⁰` is given by Theorem 1.

1. P.1 (minimize (2.6) over admissible laws of the outputs `η(t)`) has a solution if and only if
   P.2 (minimize (4.4) over admissible laws of the distribution history `w(1), …, w(t)`) has one.
2. For every solution `(V, c⁰)` of the functional equation (3.28), the law `u(t) = c⁰(w(t), t)` is
   optimal for P.1 (with `w(t)` computed from the outputs by (3.25) under this law) and for P.2,
   among all admissible laws of each problem, and both minimal values equal
   `E_{η₁} V₁(w(1)) = Σ_j P(y₁ = j) V₁(w(1) | η₁ = j)` (3.29).

**Formalization Note.** "c⁰ is given by Theorem 1" is read as: `c⁰(w, k) ∈ U` attains the minimum
in (3.28) (`IsSolution328`). On the probability simplex the solution `V` of (3.28) with
`V_{N+1} = 0` is unique and equals the cost-to-go of Theorem 1, so this is Theorem 1's minimizer. -/
theorem theorem_3 {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) :
    ((∃ c : ControlLaw Obs r, IsOptimalP1 M c) ↔ (∃ d : BeliefLaw St r, IsOptimalP2 M d)) ∧
    ∀ (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)), IsSolution328 M V c₀ →
      IsOptimalP1 M (markovLaw M c₀) ∧ IsOptimalP2 M (markovBeliefLaw M c₀) ∧
        expectedCost M (markovLaw M c₀) = ∑ j, prob1 M j * V 1 (bayes1 M j) ∧
        p2Cost M (markovBeliefLaw M c₀) = ∑ j, prob1 M j * V 1 (bayes1 M j) := by sorry

end AstromPOMDP.Reduction
