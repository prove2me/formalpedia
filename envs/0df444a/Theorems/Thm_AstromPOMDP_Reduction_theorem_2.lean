-- Prove2me | Theorems.Thm_AstromPOMDP_Reduction_theorem_2
-- name    : AstromPOMDP.Reduction.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:43:57.775105+00:00
-- url     : https://prove2.me/theorems/133c5a5b-036d-44da-ae15-41db0f218a5e
-- title:
--   Theorem 2, p. 185 — a solution of (3.28) gives an optimal law c⁰(w(t), t) for P.1 with minimal value E_{η₁} V₁(w(1))
-- statement:
--   Let $(V,c^0)$ solve the functional equation (3.28): $V_{N+1}=0$, $c^0(w,k)\in U$, and for $1\le k\le N$ and every probability vector $w$, $c^0(w,k)$ attains the minimum in
--   $$
--   V_k(w)=\min_{u\in U}\Big\{\sum_i g(u,i,k)\,w_i+\sum_j V_{k+1}\Big(\frac{z^j(u,w)}{\|z^j(u,w)\|}\Big)\|z^j(u,w)\|\Big\}.
--   $$
--   Then the control law $u(t)=c^0(w(t),t)$, with $w(t)$ computed from the outputs by (3.25), is admissible and its expected cost (2.6) is no larger than that of any admissible control law; in particular P.1 has a solution. The minimal value of (2.6) is
--   $$
--   E_{\eta_1}V_1(w(1))=\sum_j P(y_1=j)\,V_1\big(w(1)\mid\eta_1=j\big).\tag{3.29}
--   $$
--
--   This is the sufficiency half of dynamic programming: a solution of the functional equation produces an optimal feedback law that depends on the outputs only through the current conditional distribution.
--
--   **Formalization Note** "The control law $C^0$", which Theorem 2 does not define, is the law $c^0(w(t),t)$ built from the minimizer in (3.28).
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), DOI 10.1016/0022-247X(65)90154-X, p. 185, Theorem 2, (3.29)

import Mathlib
import Definitions.Def_AstromPOMDP_Reduction_Belief

namespace AstromPOMDP.Reduction

/-- Åström (1965), J. Math. Anal. Appl. 10:174–205, Theorem 2, p. 185: let `(V, c⁰)` solve the
functional equation (3.28) (with `V_{N+1} = 0` and `c⁰(w, k)` attaining the minimum). Then the
Markov control law `u(t) = c⁰(w(t), t)` is admissible and minimizes the functional (2.6) among all
admissible control laws, so P.1 has a solution, and the minimal value of (2.6) is
`E_{η₁} V₁(w(1)) = Σ_j P(y₁ = j) V₁(w(1) | η₁ = j)` (3.29).

**Formalization Note.** "The control law C⁰" of the theorem is not defined in Theorem 2 itself;
it is the law `c⁰(w(t), t)` built from the minimizer in (3.28), with `w(t)` computed by (3.25)
under that same law (`markovLaw`). -/
theorem theorem_2 {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}
    (M : Model St Obs r) (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ))
    (hV : IsSolution328 M V c₀) :
    IsOptimalP1 M (markovLaw M c₀) ∧
      expectedCost M (markovLaw M c₀) = ∑ j, prob1 M j * V 1 (bayes1 M j) := by sorry

end AstromPOMDP.Reduction
