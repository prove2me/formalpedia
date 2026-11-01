-- Prove2me | Theorems.Thm_BernoulliPoA_subcase_2_2
-- name    : BernoulliPoA.subcase_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:46:08.790143+00:00
-- url     : https://prove2.me/theorems/27ca62e6-8082-427c-b489-b462feb2320d
-- title:
--   Proof of Theorem 3, Sub-case 2.2, pp.ec6–ec7 — two binding triples
-- statement:
--   Let $\mathcal C$ be a family of nonnegative nondecreasing costs, $q\in(0,1]$, $c_1,c_2\in\mathcal C$ positive at every load $\ge1$, $k_1,k_2\ge1$, $m_1,m_2\in\mathbb N$ and $\eta\in[0,1]$ with
--   $$
--   \eta\,m_1c_1^q(m_1)+(1-\eta)\,m_2c_2^q(m_2)=\eta\,\frac1q\,k_1c_1^q(1+m_1)+(1-\eta)\,\frac1q\,k_2c_2^q(1+m_2).
--   $$
--   Then for each
--   $$
--   M<\frac{\eta\,m_1c_1^q(m_1)+(1-\eta)\,m_2c_2^q(m_2)}{\eta\,k_1c_1(k_1)+(1-\eta)\,k_2c_2(k_2)}
--   $$
--   there is a Bernoulli congestion game $\Gamma^{\mathbf p}\in\mathcal G(\mathcal C,q)$ with homogeneous probabilities $p_i\equiv q$ such that $\mathsf{PPoA}(\Gamma^{\mathbf p})>M$.
--
--   This is the lower bound of the goal theorem when the minimum of $\Psi_{\mathcal F}$ is attained at $\bar\omega>0$.
--
--   Differences from the source:
--   - generalization: two triples of F satisfying (EC.15)–(EC.17), η with (EC.18), and M < γpr(F) = left side of (EC.26) → any two triples, η with (EC.18), and M below the left side of (EC.26); reason: the source's construction uses only these facts, and (EC.15)–(EC.18) make the source's case an instance
--   - reading: (26) fixes no value for C(s)/C_pr when both vanish, while (6) sets PoA := 1 for deterministic games → ratio in ℝ≥0∞, with x/0 = ⊤ for x > 0 and 0/0 = 0; reason: x/0 = ⊤ is the value used in Case 1 (p.ec3); with 0/0 := 1 the theorem fails for C ⊆ {c₀}, where γ_pr = 0, and the two conventions give the same supremum as soon as C has a function nonzero at a positive load
--   - generalization: c : ℕ → [0,∞) nondecreasing → c : ℕ → ℝ nonnegative and nondecreasing on the loads k ≥ 1, c(0) free; reason: no quantity reads c(0), and every family of the source satisfies this condition
--   - encoding: expectations over the Bernoulli participation variables W_i → finite sums over the realized set I with weights p(I); reason: these are the source's own forms (13), (14), (24), (25), and p(I) is the law of I
--   - encoding: S_i ⊆ 2^E, nonemptiness left implicit → every strategy set of the constructed game is nonempty (InClassQ); reason: the source's games have strategy profiles; requiring it of the constructed game only strengthens the conclusion
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, proof of Theorem 3, Sub-case 2.2, displays (EC.18) and (EC.26), pp.ec6–ec7

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_BernoulliPoA_IsCostClass
import Definitions.Def_BernoulliPoA_binomExp
import Definitions.Def_BernoulliPoA_PPoA
import Definitions.Def_BernoulliPoA_InClassQ
open CongestionPoA.AsymSum

namespace BernoulliPoA

/-- **Proof of Theorem 3, Sub-case 2.2.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, proof of Theorem 3, Sub-case 2.2, (EC.18), (EC.26), pp.ec6–ec7: if two triples `(c₁, k₁, m₁)`, `(c₂, k₂, m₂)` and `η ∈ [0, 1]` satisfy (EC.18), then for each `M` below
the left side of (EC.26) there is a Bernoulli congestion game with costs in `C`, homogeneous probabilities `p_i ≡ q` and `PPoA(Γ^p) > M`.

**Formalization Note** The paper applies this with (EC.26) equal to `γ_pr(F) > M`. The games use only the costs `c₁, c₂ ∈ C`. -/
theorem subcase_2_2 {C : Set (ℕ → ℝ)} (hC : IsCostClass C) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    {c₁ c₂ : ℕ → ℝ} (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hc₁pos : ∀ j, 1 ≤ j → 0 < c₁ j) (hc₂pos : ∀ j, 1 ≤ j → 0 < c₂ j)
    {k₁ k₂ m₁ m₂ : ℕ} (hk₁ : 1 ≤ k₁) (hk₂ : 1 ≤ k₂) {η : ℝ} (hη : 0 ≤ η ∧ η ≤ 1)
    (hEC18 : η * m₁ * binomExp c₁ q m₁ + (1 - η) * m₂ * binomExp c₂ q m₂ =
      η * (1 / q) * k₁ * binomExp c₁ q (1 + m₁) + (1 - η) * (1 / q) * k₂ * binomExp c₂ q (1 + m₂))
    {M : ℝ}
    (hM : M < (η * m₁ * binomExp c₁ q m₁ + (1 - η) * m₂ * binomExp c₂ q m₂) /
      (η * k₁ * c₁ k₁ + (1 - η) * k₂ * c₂ k₂)) :
    ∃ (n r : ℕ) (G : CongestionGame (Fin n) (Fin r)) (p : Fin n → ℝ),
      InClassQ C q G p ∧ (∀ i, p i = q) ∧ ENNReal.ofReal M < PPoA G p := by sorry

end BernoulliPoA
