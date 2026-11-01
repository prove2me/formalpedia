-- Prove2me | Theorems.Thm_BernoulliPoA_case_1
-- name    : BernoulliPoA.case_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:45:59.034334+00:00
-- url     : https://prove2.me/theorems/519a9a47-1682-4351-9348-3f3d3b799644
-- title:
--   Proof of Theorem 3, Case 1, pp.ec2–ec3 — a game with $\mathsf{PPoA}=\infty$
-- statement:
--   Let $\mathcal C$ be a family of nonnegative nondecreasing costs and $q\in(0,1]$. If $c(k)=0$ for some $c\in\mathcal C\setminus\{c_0\}$ and some $k\ge1$, there is a Bernoulli congestion game $\Gamma^{\mathbf p}\in\mathcal G(\mathcal C,q)$ with homogeneous probabilities $p_i\equiv q$ such that
--   $$
--   \mathsf{PPoA}(\Gamma^{\mathbf p})=\infty.
--   $$
--
--   This settles the goal theorem in the degenerate case, where $\gamma_{\mathsf{pr}}(\mathcal C,q)=\infty$.
--
--   Differences from the source:
--   - generalization: c : ℕ → [0,∞) nondecreasing → c : ℕ → ℝ nonnegative and nondecreasing on the loads k ≥ 1, c(0) free; reason: no quantity reads c(0), and every family of the source satisfies this condition
--   - encoding: expectations over the Bernoulli participation variables W_i → finite sums over the realized set I with weights p(I); reason: these are the source's own forms (13), (14), (24), (25), and p(I) is the law of I
--   - encoding: c ∈ C \ {c0} → c is nonzero at some load k ≥ 1; reason: c(0) is free in the Lean family
--   - encoding: S_i ⊆ 2^E, nonemptiness left implicit → every strategy set of the constructed game is nonempty (InClassQ); reason: the source's games have strategy profiles; requiring it of the constructed game only strengthens the conclusion
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, proof of Theorem 3, Case 1, pp.ec2–ec3

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_IsCostClass
import Definitions.Def_BernoulliPoA_PPoA
import Definitions.Def_BernoulliPoA_InClassQ
open CongestionPoA.AsymSum

namespace BernoulliPoA

/-- **Proof of Theorem 3, Case 1.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, proof of Theorem 3, Case 1, pp.ec2–ec3: if `c(k) = 0` for some `c ∈ C \ {c₀}` and `k ≥ 1`, there is a Bernoulli congestion game
with costs in `C` and homogeneous probabilities `p_i ≡ q` such that `PPoA(Γ^p) = ∞`. -/
theorem case_1 {C : Set (ℕ → ℝ)} (hC : IsCostClass C) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    {c : ℕ → ℝ} (hc : c ∈ C) (hc0 : ∃ j, 1 ≤ j ∧ c j ≠ 0) {k : ℕ} (hk : 1 ≤ k) (hck : c k = 0) :
    ∃ (n r : ℕ) (G : CongestionGame (Fin n) (Fin r)) (p : Fin n → ℝ),
      InClassQ C q G p ∧ (∀ i, p i = q) ∧ PPoA G p = ⊤ := by sorry

end BernoulliPoA
