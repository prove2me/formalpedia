-- Prove2me | Theorems.Thm_BertsekasDP_ssp_policy_evaluation
-- name    : BertsekasDP.ssp_policy_evaluation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:43:14.097295+00:00
-- url     : https://prove2.me/theorems/70733295-896a-49f3-b576-a31db82aa804
-- title:
--   Policy evaluation (Prop. 7.2.1(c))
-- statement:
--   **Proposition 7.2.1(c) (policy evaluation).** Under Assumption 7.2.1, let $\mu$ be any admissible stationary policy. Then its cost vector $J_\mu$ is the unique solution of the linear system
--
--   $$J_\mu(i) \;=\; g\bigl(i, \mu(i)\bigr) \;+\; \sum_{j=1}^{n} p_{ij}\bigl(\mu(i)\bigr) J_\mu(j), \qquad i = 1, \dots, n,$$
--
--   the iteration $J_{k+1} = T_\mu J_k$ converges to $J_\mu$ from every initial vector, and $J_\mu$ is the limit of the $N$-stage costs of $\mu$:
--
--   $$\lim_{k \to \infty} (T_\mu^k J_0)(i) \;=\; J_\mu(i) \;=\; \lim_{N \to \infty} J^N_{\mu}(i) \qquad \text{for every } i .$$
--
--   This is the single-policy case of the main theorem, and the computational workhorse of policy iteration: evaluating a policy is solving one linear system of $n$ equations, or equivalently iterating a contraction. That the same vector is both the fixed point and the limit of finite-horizon costs is what makes the two views of "the cost of $\mu$" interchangeable.
--
--   **Formalization Note** Uniqueness is asserted among all real-valued vectors. Under Assumption 7.2.1 the operator $T_\mu$ is a contraction after $m$ stages rather than after one, which is where the finiteness of the policy space enters the proof.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 7.2.1(c)

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace BertsekasDP

theorem ssp_policy_evaluation {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C)
    (hA : ∃ m : ℕ, 0 < m ∧ ∀ π, BertsekasSSPAdmissible M π →
      ∀ i, BertsekasSSPSurvival M π m i < 1)
    (μ : Fin n → C) (hμ : ∀ i, μ i ∈ M.U i) :
    ∃ Jμ : Fin n → ℝ,
      BertsekasSSPPolicyOp M μ Jμ = Jμ ∧
      (∀ J : Fin n → ℝ, BertsekasSSPPolicyOp M μ J = J → J = Jμ) ∧
      (∀ J₀ : Fin n → ℝ,
        Filter.Tendsto (fun k => (BertsekasSSPPolicyOp M μ)^[k] J₀)
          Filter.atTop (nhds Jμ)) ∧
      (∀ i, Filter.Tendsto (fun N => BertsekasSSPNCost M (fun _ => μ) N i)
        Filter.atTop (nhds (Jμ i))) := by sorry

end BertsekasDP
