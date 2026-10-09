-- Prove2me | Theorems.Thm_BanditCovariates_ABSE_theorem_5_1
-- name    : BanditCovariates.ABSE.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:09:27.280487+00:00
-- url     : https://prove2.me/theorems/6577bfec-4850-4f79-94c1-8c81a37b8bcb
-- title:
--   Theorem 5.1, p. 22 — ABSE has 𝔼Rₙ ≤ Cn(K log K/n)^{β(α+1)/(2β+d)} for α < ∞
-- statement:
--   Fix $d\ge1$, $0<\beta\le1$, $L>0$, $\alpha>0$ with $\alpha\beta\le d$, margin constants $0<\delta_0<1$ and $C_0>0$, and density bounds $0<\underline c\le\bar c$. There is a constant $C>0$, depending only on these parameters, such that the following holds for every number of arms $K\ge2$ and every horizon $n\ge K\log K$. Let the machine belong to the class $\mathcal M^K_{\mathcal X}(\alpha,\beta,L)$: covariates i.i.d. on $\mathcal X=[0,1]^d$ with a density between $\underline c$ and $\bar c$, rewards in $[0,1]$ with $(\beta,L)$-Hölder conditional means $f^{(i)}$ (Euclidean norm), and
--
--   $$P_X\big(0<f^\star(X)-f^\sharp(X)\le\delta\big)\le C_0\delta^\alpha\qquad(0\le\delta\le\delta_0).$$
--
--   Then the adaptively binned successive elimination policy $\tilde\pi$ (Policy 3), which knows only $d,\beta,L,K,n$, satisfies
--
--   $$\mathbb E R_n(\tilde\pi)\le C\,n\left(\frac{K\log K}{n}\right)^{\beta(\alpha+1)/(2\beta+d)}.$$
--
--   This is the paper's main result: one policy that adapts its partition to the data attains the minimax rate of the class.
--
--   **Formalization Note** The hypothesis $\alpha\beta\le d$ is added. The printed finite-$\alpha$ claim omits it, and the proof invokes it. Without it the claim is false: for $K=2$, $d=\beta=1$, $f^{(1)}\equiv1$, $f^{(2)}\equiv0$ the margin condition holds for every $\alpha$, the policy pulls both arms in its first round so $\mathbb E R_n\ge1$, but for $\alpha=10$ the right side tends to $0$. The constant is quantified after the class parameters and before $K$, $n$ and the machine. Reward vectors are independent over time but not assumed identically distributed, as in §3.1. The regret is the pseudo-regret $\sum_t\mathbb E[f^\star(X_t)-f^{(\tilde\pi_t)}(X_t)]$, the paper's second expression in §3.1.
-- source:
--   Perchet, Rigollet, The multi-armed bandit problem with covariates, arXiv:1110.6084v3, p. 22, Theorem 5.1, α < ∞ clause; αβ ≤ d added per paper.md slip 8

import Mathlib
import Definitions.Def_BanditCovariates_ABSE_Policy

noncomputable section

namespace BanditCovariates.ABSE

/-- Theorem 5.1, p. 22, finite-margin regime. The necessary restriction
αβ ≤ d makes explicit the regime used in the paper's proof. -/
theorem theorem_5_1 (d : ℕ) (β L α δ₀ C₀ cLow cHigh : ℝ)
    (hd : 1 ≤ d) (hβ : 0 < β) (hβ1 : β ≤ 1) (hL : 0 < L)
    (hα : 0 < α) (hregime : α * β ≤ (d : ℝ))
    (hδ₀ : 0 < δ₀) (hδ₀1 : δ₀ < 1) (hC₀ : 0 < C₀)
    (hcLow : 0 < cLow) (hcHigh : cLow ≤ cHigh) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K n : ℕ) (hK : 2 ≤ K),
      (K : ℝ) * Real.log (K : ℝ) ≤ (n : ℝ) →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (M : Machine d K Ω),
        InClass M β L α δ₀ C₀ cLow cHigh →
        regret (n := n) M (by omega) β L ≤
          C * (n : ℝ) *
            (((K : ℝ) * Real.log (K : ℝ) / (n : ℝ)) ^
              (β * (α + 1) / (2 * β + (d : ℝ)))) := by sorry

end BanditCovariates.ABSE
