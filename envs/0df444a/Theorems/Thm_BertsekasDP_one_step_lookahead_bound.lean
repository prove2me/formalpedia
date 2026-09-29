-- Prove2me | Theorems.Thm_BertsekasDP_one_step_lookahead_bound
-- name    : BertsekasDP.one_step_lookahead_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-11T01:35:11.550792+00:00
-- url     : https://prove2.me/theorems/56510ff5-3a9b-47ff-8497-848e3effe888
-- title:
--   One-step lookahead performance bound (Prop. 6.3.1)
-- statement:
--   **Proposition 6.3.1 (performance bound for one-step lookahead policies).** In the basic stochastic model, let $\tilde J_k$ be cost-to-go approximations with $\tilde J_N = g_N$, let $\bar U_k(x) \subseteq U_k(x)$ be restricted control sets, and let $\bar\pi$ be a one-step lookahead policy: $\bar\mu_k(x)$ attains
--
--   $$\hat J_k(x) \;=\; \min_{u \in \bar U_k(x)} \; \mathbb{E}_w\Bigl[g_k(x,u,w) + \tilde J_{k+1}\bigl(f_k(x,u,w)\bigr)\Bigr].$$
--
--   Assume the key condition (Eq. (6.20)) that this lookahead value never exceeds the approximation it is built from:
--
--   $$\hat J_k(x) \;\le\; \tilde J_k(x) \qquad \text{for all } x \text{ and } k < N .$$
--
--   Then the true cost-to-go $\bar J_k$ of the policy $\bar\pi$ satisfies
--
--   $$\bar J_k(x) \;\le\; \hat J_k(x) \;\le\; \tilde J_k(x) \qquad \text{for all } x \text{ and } k \le N .$$
--
--   Two things follow. First, the policy is at least as good as the approximation on which it is based — and via Example 6.3.1, taking $\tilde J$ to be the cost-to-go of a given heuristic policy shows that *rolling out any policy improves it*, the stochastic counterpart of Prop. 6.4.2. Second, $\hat J_k(x)$, which is computed anyway when the control is selected, is a readily available upper bound on the policy's true performance.
--
--   **Formalization Note** The minimization defining the policy ranges over the restricted set $\bar U_k(x)$ only, as in Eq. (6.19); the sets are required nonempty implicitly, since the policy selects from them. The conclusion is proved by backward induction and is stated for all $k \le N$, with the sharper first inequality asserted where $k < N$.
-- source:
--   D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, 3rd ed., Athena Scientific, 2005, Proposition 6.3.1

import Mathlib
import Definitions.Def_BertsekasDPModel

namespace BertsekasDP

theorem one_step_lookahead_bound {S C W : Type} [Fintype W]
    (M : BertsekasDPModel S C W)
    (Jt : ℕ → S → ℝ) (hJN : ∀ x, Jt M.N x = M.gN x)
    (Ubar : ℕ → S → Finset C)
    (hUsub : ∀ k x, Ubar k x ⊆ M.U k x)
    (π : ℕ → S → C)
    (hπmem : ∀ k x, π k x ∈ Ubar k x)
    (hπmin : ∀ k, k < M.N → ∀ x, ∀ u ∈ Ubar k x,
      ∑ w, M.p k x (π k x) w *
          (M.g k x (π k x) w + Jt (k + 1) (M.f k x (π k x) w)) ≤
        ∑ w, M.p k x u w * (M.g k x u w + Jt (k + 1) (M.f k x u w)))
    (h620 : ∀ k, k < M.N → ∀ x,
      ∑ w, M.p k x (π k x) w *
          (M.g k x (π k x) w + Jt (k + 1) (M.f k x (π k x) w)) ≤ Jt k x) :
    ∀ k, k ≤ M.N → ∀ x,
      (k < M.N →
        BertsekasDPPolicyCost M π (M.N - k) x ≤
          ∑ w, M.p k x (π k x) w *
            (M.g k x (π k x) w + Jt (k + 1) (M.f k x (π k x) w))) ∧
      BertsekasDPPolicyCost M π (M.N - k) x ≤ Jt k x := by sorry

end BertsekasDP
