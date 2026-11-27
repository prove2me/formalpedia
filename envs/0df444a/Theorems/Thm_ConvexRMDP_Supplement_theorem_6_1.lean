-- Prove2me | Theorems.Thm_ConvexRMDP_Supplement_theorem_6_1
-- name    : ConvexRMDP.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:59:51.817311+00:00
-- url     : https://prove2.me/theorems/1bdcb336-081b-4a72-bf27-011645eaa68f
-- title:
--   Theorem 6.1 — s-rectangular case: $\tilde v^\star = \log_b(\tilde x^\star)$ for the unique optimum of the convex program (6.3), and $\tilde v^\star_s \le v^\star_s \le \tilde v^\star_s + \epsilon$
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an s-rectangular robust MDP, with each $\mathcal U_s \subseteq \Delta(\mathcal S)^{\mathcal A}$ nonempty, convex and compact and $\mathcal A$ nonempty, and let $b > 0$. Let $\tilde T$ be the regularized robust Bellman operator (6.1) with $\nu_{sa} = 1/|\mathcal A|$, $\tilde t$ the operator (6.2), and $T$ the s-rectangular robust Bellman operator. Then:
--
--   1. $\tilde T$ has a unique fixed point $\tilde v^\star \in \mathbb R^{\mathcal S}$;
--   2. $\tilde v^\star = \log_b(\tilde x^\star)$, where $\tilde x^\star \in \mathbb R^{\mathcal S}$ is the unique optimal solution to the convex program
--   $$
--   \max\Big\{\sum_{s \in \mathcal S} x_s \;\Big|\; 1 \le x_s \le \tilde t(x)_s,\ \forall s \in \mathcal S\Big\}, \tag{6.3}
--   $$
--   whose feasible set is convex and closed;
--   3. if $\epsilon > 0$ and $b \ge \log(|\mathcal A|)/(\epsilon(1-\gamma))$, then for the optimal value function $v^\star$ of the s-rectangular RMDP,
--   $$
--   \tilde v^\star_s \le v^\star_s \le \tilde v^\star_s + \epsilon \qquad \text{for each } s \in \mathcal S .
--   $$
--
--   This extends Theorems 4.1 and 4.2 from sa-rectangular to s-rectangular uncertainty sets.
--
--   **Formalization Note** "Unique optimal solution" means feasible, objective-maximal, and equal to every feasible point with the same objective value. The optimal value function $v^\star$ is taken to be the fixed point of the s-rectangular robust Bellman operator $T$ printed on p.20; its identification with the max–min discounted return is a result of Wiesemann et al. (2013) that the paper cites and does not prove. $\log_b(z) = \log(z)/b$.
--
--   Differences from the source:
--   - reading: "$v^\star$ the optimal value function of the s-rectangular RMDP" → every fixed point of `SRMDP.robustOp` (the operator $T$ of p.20); reason: the paper introduces $T$ for this purpose (p.20) and its proof brackets $\tilde T$ against $T$; the equality with the max–min return is cited (Wiesemann et al. 2013), not stated in the paper.
--   - encoding: "the unique fixed point $\tilde v^\star$" (presupposed) → first clause `∃! v, regOp b v = v` and the rest for every fixed point; reason: same instances.
--   - encoding: "convex program (6.3)" → its feasible set is `Convex` and `IsClosed`; reason: the paper's definition (§1.1, p.4) with a linear objective.
--   - encoding: nonempty $\mathcal U_s$, nonempty $\mathcal A$, $b > 0$ → fields of `SRMDP` and hypotheses; reason: presupposed by the minima and maxima in (6.1)–(6.2) and by $\log_b$.
-- source:
--   Grand-Clément & Petrik, arXiv:2209.10187v2, Theorem 6.1, p.20 (operators T, (6.1), (6.2), program (6.3)); proofs in App. F

import Mathlib
import Definitions.Def_ConvexRMDP_Supplement_SRMDP_regOp
import Definitions.Def_ConvexRMDP_Supplement_SRMDP_tOp

namespace ConvexRMDP

namespace Supplement

/-- **Theorem 6.1** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.20; proofs in App. F). Let
`ṽ⋆ ∈ ℝ^S` be the unique fixed point of the s-rectangular regularized robust Bellman operator `T̃` in
(6.1). Then `ṽ⋆ = log_b(x̃⋆)`, with `x̃⋆ ∈ ℝ^S` the unique optimal solution to the convex program
`(6.3)  max {∑_s x_s | 1 ≤ x_s ≤ t̃(x)_s, ∀ s}`, with `t̃` as in (6.2). Additionally, let `ε > 0` and
`b ≥ log(|A|)/(ε(1−γ))`, and let `v⋆` be the optimal value function of the s-rectangular RMDP. Then
`ṽ⋆_s ≤ v⋆_s ≤ ṽ⋆_s + ε` for each `s ∈ S`.

**Formalization Note.** The first clause is the existence and uniqueness of the fixed point that the
theorem presupposes; the rest holds for every fixed point. "Unique optimal solution" is: feasible,
objective-maximal, and every feasible point with the same objective value equals it. "Convex
program" is: the feasible set of (6.3) is convex and closed (its objective is linear). The optimal
value function `v⋆` is read as the fixed point of the s-rectangular robust Bellman operator `T`
printed on p.20 (`SRMDP.robustOp`); its identification with the max–min discounted return is
Wiesemann et al. (2013), cited and not proved in the paper. The `𝒰_s` are nonempty convex compact
(fields of `SRMDP`), `A` is nonempty and `b > 0`. -/
theorem theorem_6_1 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : SRMDP S A) (b : ℝ) (hb : 0 < b) :
    (∃! v : S → ℝ, M.regOp b v = v) ∧
      ∀ vt : S → ℝ, M.regOp b vt = vt →
        (∃ xt : S → ℝ, (∀ s, 1 ≤ xt s ∧ xt s ≤ M.tOp b xt s) ∧
          (∀ x : S → ℝ, (∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s) → ∑ s, x s ≤ ∑ s, xt s) ∧
          (∀ x : S → ℝ, (∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s) → ∑ s, x s = ∑ s, xt s → x = xt) ∧
          vt = fun s => logB b (xt s)) ∧
        Convex ℝ {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} ∧
        IsClosed {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} ∧
        ∀ ε : ℝ, 0 < ε → Real.log (Fintype.card A) / (ε * (1 - M.γ)) ≤ b →
          ∀ vs : S → ℝ, M.robustOp vs = vs → ∀ s, vt s ≤ vs s ∧ vs s ≤ vt s + ε := by sorry

end Supplement

end ConvexRMDP
