-- Prove2me | Theorems.Thm_ConvexRMDP_theorem_4_1
-- name    : ConvexRMDP.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:18:21.5371+00:00
-- url     : https://prove2.me/theorems/e2851c7f-43ae-42a3-85c8-f8974daef06e
-- title:
--   Theorem 4.1: $\tilde v^\star$ uniquely solves (4.6), and $\tilde v^\star = \log_b(\tilde x^\star)$ for the unique optimum $\tilde x^\star$ of the convex program (4.7)
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP: finite $\mathcal S$ and nonempty finite $\mathcal A$, rewards $r_{sa} \ge 0$, discount $\gamma \in (0,1)$, nonempty uncertainty sets $\mathcal U_{sa} \subseteq \Delta(\mathcal S)$. Let $b > 0$, let $\tilde T$ be the regularized robust Bellman operator with uniform reference policy and $\tilde t$ the operator (4.5). Then:
--
--   1. $\tilde T$ has a unique fixed point $\tilde v^\star$.
--   2. $\tilde v^\star$ is the unique optimal solution of the (potentially) non-convex program
--   $$
--   \max\Big\{\sum_{s \in \mathcal S} \exp_b(v_s) \;\Big|\; v \le \tilde T(v),\ v \in \mathbb R^{\mathcal S}\Big\}. \tag{4.6}
--   $$
--   3. The program
--   $$
--   \max\Big\{\sum_{s \in \mathcal S} x_s \;\Big|\; 1 \le x_s \le \tilde t(x)_s,\ \forall s \in \mathcal S\Big\} \tag{4.7}
--   $$
--   has a unique optimal solution $\tilde x^\star$, and $\tilde v^\star = \log_b(\tilde x^\star)$, i.e. $\tilde v^\star_s = \log(\tilde x^\star_s)/b$ for every $s$.
--   4. (4.7) is a convex program: its objective is linear and its feasible set is convex and closed.
--
--   "Unique optimal solution" means: feasible, with maximal objective value, and every feasible point with the same objective value equals it. Here $\exp_b(z) = e^{bz}$ and $\log_b(z) = \log(z)/b$ ($b$ is not the base of the logarithm).
--
--   The theorem is the paper's convex formulation of robust MDPs: the fixed point of the entropy-regularized robust Bellman operator, which approximates the robust value function within $\log|\mathcal A|/(b(1-\gamma))$, is recovered by solving a convex program with $|\mathcal S|$ variables and $2|\mathcal S|$ constraints.
--
--   Differences from the source:
--   - generalization: min over p ∈ 𝒰_sa (the paper's min presupposes attainment) → infimum (sInf) over an arbitrary nonempty 𝒰_sa ⊆ Δ(S); reason: the set is nonempty and bounded below; whenever the minimum is attained the infimum equals it, so the statement specializes to the source's.
--   - reading: 𝒰_sa ⊆ Δ(S) with min_{p ∈ 𝒰_sa} → 𝒰_sa nonempty (field U_nonempty of RMDP); reason: a minimum over an empty set is undefined; the paper's formulas presuppose nonemptiness.
--   - reading: A finite → A finite and nonempty; reason: Δ(A) is empty otherwise and the maximum in (4.1) is undefined.
--   - encoding: max over π_s ∈ Δ(A) in (4.1) → sSup over stdSimplex ℝ A; reason: the set is nonempty and bounded above and the maximum is attained (Lemma 4.1); same value.
--   - reading: "(4.7) is a convex program" → its feasible set is convex and closed (objective linear); reason: §1.1, p.4 defines a convex formulation as minimizing a convex (maximizing a concave) function over a closed, convex set.
--   - encoding: Suppose that ṽ⋆ is the unique fixed point of T̃ → ∃! fixed point, and the conclusions for every fixed point; reason: the existence and uniqueness the theorem presupposes is stated as its first clause, so no conclusion rests on an unproved assumption.
--   - encoding: ṽ⋆ (resp. x̃⋆) is the unique optimal solution → feasible, objective maximal, and every feasible point with the same objective value equals it; reason: the definition of a unique optimal solution.
--   - encoding: ℝ^S with componentwise order and ℓ∞ norm → S → ℝ with the Pi order and the sup metric; reason: Lean convention; identical order and metric.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), Theorem 4.1, p.14 (programs (4.6) and (4.7)); convex program as defined in §1.1, p.4

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_RMDP_tOp

namespace ConvexRMDP

/-- **Theorem 4.1** (Grand-Clément & Petrik, arXiv:2209.10187v2, p.14). Let `ṽ⋆` be the unique fixed
point of the regularized robust Bellman operator `T̃`. Then `ṽ⋆` is the unique optimal solution of
the (potentially) non-convex program
`(4.6)  max { ∑_s exp_b(v_s) | v ≤ T̃(v), v ∈ ℝ^S }`.
Additionally `ṽ⋆ = log_b(x̃⋆)`, where `x̃⋆` is the unique optimal solution of the convex program
`(4.7)  max { ∑_s x_s | 1 ≤ x_s ≤ t̃(x)_s, ∀ s }`.

**Formalization Note.** The first clause is the existence and uniqueness of the fixed point that
the theorem presupposes; the rest holds for every fixed point. "Unique optimal solution" is:
feasible, objective-maximal, and every feasible point with the same objective value equals it.
"Convex program" (§1.1, p.4: a concave objective maximized over a closed convex set) is the last
clause: the feasible set of (4.7) is convex and closed (its objective is linear).
`log_b(z) = log(z)/b`, `exp_b(z) = exp(b z)`; `ℝ^S` is `S → ℝ` with componentwise order.
`A` is nonempty and `b > 0`; the model's standing assumptions are the fields of `RMDP`. -/
theorem theorem_4_1 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    (∃! v : S → ℝ, M.regOp b v = v) ∧
      ∀ vt : S → ℝ, M.regOp b vt = vt →
        (IsGreatest ((fun v : S → ℝ => ∑ s, expB b (v s)) '' {v | v ≤ M.regOp b v})
            (∑ s, expB b (vt s)) ∧
          ∀ v : S → ℝ, v ≤ M.regOp b v → ∑ s, expB b (v s) = ∑ s, expB b (vt s) → v = vt) ∧
        (∃ xt : S → ℝ, (∀ s, 1 ≤ xt s ∧ xt s ≤ M.tOp b xt s) ∧
          (∀ x : S → ℝ, (∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s) → ∑ s, x s ≤ ∑ s, xt s) ∧
          (∀ x : S → ℝ, (∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s) → ∑ s, x s = ∑ s, xt s → x = xt) ∧
          vt = fun s => logB b (xt s)) ∧
        Convex ℝ {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} ∧
        IsClosed {x : S → ℝ | ∀ s, 1 ≤ x s ∧ x s ≤ M.tOp b x s} := by sorry

end ConvexRMDP
