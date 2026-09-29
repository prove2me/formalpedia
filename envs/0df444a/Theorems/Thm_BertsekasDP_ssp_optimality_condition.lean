-- Prove2me | Theorems.Thm_BertsekasDP_ssp_optimality_condition
-- name    : BertsekasDP.ssp_optimality_condition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-08T00:43:49.164776+00:00
-- url     : https://prove2.me/theorems/85ded809-6bcb-4362-948b-49b44241fc71
-- title:
--   Optimality condition (Prop. 7.2.1(d))
-- statement:
--   **Proposition 7.2.1(d) (optimality condition).** Under Assumption 7.2.1, let $J^*$ solve Bellman's equation and let $\mu$ be an admissible stationary policy with evaluated cost $J_\mu$. Then $\mu$ is optimal **if and only if** it attains the minimum in Bellman's equation at every state:
--
--   $$J_\mu = J^* \qquad \Longleftrightarrow \qquad g\bigl(i, \mu(i)\bigr) + \sum_{j=1}^{n} p_{ij}\bigl(\mu(i)\bigr) J^*(j) \;=\; \min_{u \in U(i)} \Bigl[\, g(i,u) + \sum_{j=1}^{n} p_{ij}(u) J^*(j) \,\Bigr] \quad \text{for all } i .$$
--
--   In words: the optimal policies are exactly the policies that are **greedy** with respect to the optimal cost vector. This is what turns the solution of Bellman's equation into a controller — one reads off an optimal policy by minimizing state by state — and it is the criterion by which policy iteration recognizes that it has finished.
--
--   **Formalization Note** $J^*$ and $J_\mu$ enter as given fixed points of $T$ and $T_\mu$ respectively; their uniqueness is not assumed here, being supplied by Prop. 7.2.1(b),(c). Both directions of the equivalence are asserted.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 7.2.1(d)

import Mathlib
import Definitions.Def_BertsekasSSPModel

namespace BertsekasDP

theorem ssp_optimality_condition {n : ℕ} {C : Type} [Fintype C]
    (M : BertsekasSSPModel n C)
    (hA : ∃ m : ℕ, 0 < m ∧ ∀ π, BertsekasSSPAdmissible M π →
      ∀ i, BertsekasSSPSurvival M π m i < 1)
    (Jstar : Fin n → ℝ) (hbell : BertsekasSSPBellmanOp M Jstar = Jstar)
    (μ : Fin n → C) (hμ : ∀ i, μ i ∈ M.U i)
    (Jμ : Fin n → ℝ) (heval : BertsekasSSPPolicyOp M μ Jμ = Jμ) :
    Jμ = Jstar ↔
      ∀ i, M.g i (μ i) + ∑ j, M.p i (μ i) j * Jstar j =
        BertsekasSSPBellmanOp M Jstar i := by sorry

end BertsekasDP
