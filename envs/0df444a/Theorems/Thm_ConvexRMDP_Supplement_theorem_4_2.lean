-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_theorem_4_2
-- name    : ConvexRMDP.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:56:36.213482+00:00
-- url     : https://prove2.me/theorems/9efc439a-237f-5132-aacb-a877640861df
-- title:
--   Theorem 4.2 — for $b \ge \log(|\mathcal A|)/(\epsilon(1-\gamma))$, $\tilde v^\star = \log_b(\tilde x^\star)$ satisfies $\tilde v^\star_s \le v^\star_s \le \tilde v^\star_s + \epsilon$
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP with $\mathcal A$ nonempty, and let $v^\star$ be the fixed point of the robust Bellman operator $T$. Suppose that $\epsilon > 0$ and that the regularization scalar $b > 0$ satisfies
--
--   $$
--   b \ge \frac{\log(|\mathcal A|)}{\epsilon\,(1-\gamma)} .
--   $$
--
--   Let $\tilde x^\star \in \mathbb R^{\mathcal S}$ be an optimal solution to the convex program (4.7), $\max\{\sum_s x_s : 1 \le x_s \le \tilde t(x)_s,\ \forall s\}$, and let $\tilde v^\star = \log_b(\tilde x^\star)$, i.e. $\tilde v^\star_s = \log(\tilde x^\star_s)/b$. Then
--
--   $$
--   \tilde v^\star_s \le v^\star_s \le \tilde v^\star_s + \epsilon \qquad \text{for each } s \in \mathcal S .
--   $$
--
--   Solving the convex program (4.7) thus yields the robust value function up to any prescribed accuracy $\epsilon$.
--
--   **Formalization Note** "Optimal solution" means feasible for (4.7) and with maximal objective among feasible points. $\tilde t$ is the published `ConvexRMDP.RMDP.tOp` and $\log_b$ the published `ConvexRMDP.logB`.
--
--   Differences from the source:
--   - encoding: "$\tilde x^\star$ an optimal solution to (4.7)" → hypotheses: `xt` feasible and `∑ x ≤ ∑ xt` for every feasible `x`; reason: the definition of an optimal solution.
--   - encoding: $v^\star$ "the fixed-point of $T$" → every `vs` with `robustOp M vs = vs`; reason: the fixed point is unique, same instances.
--   - encoding: $b > 0$ → hypothesis `0 < b` beside the printed bound; reason: $\log_b$ is defined for $b > 0$ only (p.12, "For $b > 0$"); the bound alone gives only $b \ge 0$ when $|\mathcal A| = 1$, a value outside the paper's domain.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Theorem 4.2, p.14

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_tOp
import Definitions.Def_ConvexRMDP_Supplement_robustOp

namespace ConvexRMDP

namespace Supplement

/-- **Theorem 4.2** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.14). Suppose that `ε > 0` and
`b ≥ log(|A|)/(ε(1−γ))`. Let `x̃⋆ ∈ ℝ^S` be an optimal solution to (4.7),
`max {∑_s x_s | 1 ≤ x_s ≤ t̃(x)_s, ∀ s}`, and let `ṽ⋆ = log_b(x̃⋆)`. Then `ṽ⋆_s ≤ v⋆_s ≤ ṽ⋆_s + ε` for each
`s ∈ S`, where `v⋆` is the fixed point of the robust Bellman operator `T` (p.14: "`v⋆`, the
fixed-point of `T`").

**Formalization Note.** "Optimal solution" is: feasible for (4.7) and objective-maximal among
feasible points; the conclusion is asserted for every such `x̃⋆` and every fixed point `v⋆` of
`T = robustOp`. `log_b(z) = log(z)/b` is the published `logB`. The regularization scalar satisfies
`b > 0` (standing assumption of §4; when `|A| = 1` the printed bound alone only gives `b ≥ 0`). `A` is
nonempty. -/
theorem theorem_4_2 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b ε : ℝ) (hb : 0 < b) (hε : 0 < ε)
    (hbε : Real.log (Fintype.card A) / (ε * (1 - M.γ)) ≤ b)
    (xt : S → ℝ) (hxt_feas : ∀ s, 1 ≤ xt s ∧ xt s ≤ M.tOp b xt s)
    (hxt_opt : ∀ x : S → ℝ, (∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s) → ∑ s, x s ≤ ∑ s, xt s)
    (vs : S → ℝ) (hvs : robustOp M vs = vs) (s : S) :
    logB b (xt s) ≤ vs s ∧ vs s ≤ logB b (xt s) + ε := by sorry

end Supplement

end ConvexRMDP
