-- Prove2me | Theorems.Thm_BernoulliPoA_subcase_2_1
-- name    : BernoulliPoA.subcase_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:46:11.927369+00:00
-- url     : https://prove2.me/theorems/7d675508-7df5-48d6-bad2-147f9c4139ed
-- title:
--   Proof of Theorem 3, Sub-case 2.1, pp.ec4–ec6 — one binding triple
-- statement:
--   Let $\mathcal C$ be a family of nonnegative nondecreasing costs, $q\in(0,1]$, $c\in\mathcal C$ with $c(j)>0$ for all $j\ge 1$, $k\ge 1$ and $m\in\mathbb N$ with
--   $$
--   \frac1q\,k\,c^q(1+m)\ge m\,c^q(m).
--   $$
--   Then for each $M<\dfrac{m\,c^q(m)}{k\,c(k)}$ there is a Bernoulli congestion game $\Gamma^{\mathbf p}\in\mathcal G(\mathcal C,q)$ with homogeneous probabilities $p_i\equiv q$ such that $\mathsf{PPoA}(\Gamma^{\mathbf p})>M$.
--
--   This is the lower bound of the goal theorem when the minimum of $\Psi_{\mathcal F}$ is attained at $\bar\omega=0$.
--
--   Differences from the source:
--   - generalization: a triple of the finite family F with β(0) = γpr(F) and β′(0) ≥ 0, and M < γpr(F) → any triple with (1/q) k cq(1+m) ≥ m cq(m), and M < m cq(m)/(k c(k)); reason: the source's construction uses only these two facts, and (EC.8) makes the source's case an instance
--   - reading: (26) fixes no value for C(s)/C_pr when both vanish, while (6) sets PoA := 1 for deterministic games → ratio in ℝ≥0∞, with x/0 = ⊤ for x > 0 and 0/0 = 0; reason: x/0 = ⊤ is the value used in Case 1 (p.ec3); with 0/0 := 1 the theorem fails for C ⊆ {c₀}, where γ_pr = 0, and the two conventions give the same supremum as soon as C has a function nonzero at a positive load
--   - generalization: c : ℕ → [0,∞) nondecreasing → c : ℕ → ℝ nonnegative and nondecreasing on the loads k ≥ 1, c(0) free; reason: no quantity reads c(0), and every family of the source satisfies this condition
--   - encoding: expectations over the Bernoulli participation variables W_i → finite sums over the realized set I with weights p(I); reason: these are the source's own forms (13), (14), (24), (25), and p(I) is the law of I
--   - encoding: S_i ⊆ 2^E, nonemptiness left implicit → every strategy set of the constructed game is nonempty (InClassQ); reason: the source's games have strategy profiles; requiring it of the constructed game only strengthens the conclusion
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, proof of Theorem 3, Sub-case 2.1, displays (EC.8) and (EC.14), pp.ec4–ec6

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_IsCostClass
import Definitions.Def_BernoulliPoA_binomExp
import Definitions.Def_BernoulliPoA_PPoA
import Definitions.Def_BernoulliPoA_InClassQ
open CongestionPoA.AsymSum

namespace BernoulliPoA

/-- **Proof of Theorem 3, Sub-case 2.1.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, proof of Theorem 3, Sub-case 2.1, (EC.8), (EC.14), pp.ec4–ec6: if a triple `(c, k, m)` satisfies `(1/q) k c^q(1 + m) ≥ m c^q(m)`, then for each
`M < m c^q(m) / (k c(k))` there is a Bernoulli congestion game with costs in `C`, homogeneous probabilities `p_i ≡ q` and `PPoA(Γ^p) > M`.

**Formalization Note** The paper applies this with `m c^q(m) / (k c(k)) = γ_pr(F) > M`. The games use only the cost `c ∈ C`. -/
theorem subcase_2_1 {C : Set (ℕ → ℝ)} (hC : IsCostClass C) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    {c : ℕ → ℝ} (hc : c ∈ C) (hcpos : ∀ j, 1 ≤ j → 0 < c j) {k m : ℕ} (hk : 1 ≤ k)
    (hslope : (m : ℝ) * binomExp c q m ≤ (1 / q) * k * binomExp c q (1 + m))
    {M : ℝ} (hM : M < (m : ℝ) * binomExp c q m / ((k : ℝ) * c k)) :
    ∃ (n r : ℕ) (G : CongestionGame (Fin n) (Fin r)) (p : Fin n → ℝ),
      InClassQ C q G p ∧ (∀ i, p i = q) ∧ ENNReal.ofReal M < PPoA G p := by sorry

end BernoulliPoA
