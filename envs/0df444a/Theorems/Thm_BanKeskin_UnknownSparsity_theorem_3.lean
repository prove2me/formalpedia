-- Prove2me | Theorems.Thm_BanKeskin_UnknownSparsity_theorem_3
-- name    : BanKeskin.UnknownSparsity.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:51.389757+00:00
-- url     : https://prove2.me/theorems/7f9a7bac-ab52-46be-924e-88edc1111113
-- title:
--   Theorem 3, p. 5558 — ILQX(m₁, m₂, λ) has expected regret ≤ C̃ s√T(log d + log T) for all θ ∈ Θ and T ≥ 2
-- statement:
--   Consider the personalized dynamic pricing model of Ban and Keskin (2021): a customer with augmented features $X_t = [1;Z_t]\in\mathbb R^{d+1}$ arrives in period $t$, the seller charges $p_t\in[\ell,u]$ and observes the demand $D_t = g(\alpha\cdot X_t + (\beta\cdot X_t)p_t)+\varepsilon_t$ with unknown $\theta=(\alpha,\beta)$ in a compact rectangle $\Theta$, under the standing assumptions of §2 (i.i.d. bounded mean-zero features with positive definite covariance, sub-Gaussian martingale-difference shocks, a differentiable increasing link with derivative bounded between $\tilde\ell>0$ and $\tilde u$ on the relevant domain, and an interior clairvoyant price $\varphi$). The sparsity $s = s(\theta)$ is the number of indices $i$ with $\alpha_i\ne0$ or $\beta_i\ne0$.
--
--   Fix $\tilde c>0$ and let $\pi = \mathrm{ILQX}(m_1,m_2,\lambda)$ with $\lambda_{t+1} = \tilde c\,t^{1/4}\sqrt{\log d+\log t}$: experimental prices $m_1, m_2$ on the periods $M_1, M_2$ of (7), and otherwise the price $\varphi(\mathcal P_\Theta\hat\theta^{(\mathrm{lasso})}_t(\lambda_t), X_t)$ at the projected lasso quasi-likelihood estimate (17)–(19). Then there is a finite positive constant $\tilde C$ such that
--
--   $$\Delta^\pi_\theta(T) \ \le\ \tilde C\, s\sqrt T\,(\log d+\log T)\qquad\text{for all }\theta\in\Theta\text{ and }T\ge2,$$
--
--   where $\Delta^\pi_\theta(T) = \mathbb E\big[\sum_{t=1}^T r^*(\theta,X_t) - r(p_t,\theta,X_t)\big]$ is the expected regret (4) against the clairvoyant who charges $\varphi(\theta,X_t)$.
--
--   Together with the paper's lower bound of order $s\sqrt T$ for the linear model (Theorem 1), this shows that ILQX is first-order optimal up to logarithmic factors, without knowledge of the sparsity pattern and for a general link.
--
--   **Formalization Note.** $\tilde C$ is chosen after the model, the probability space, the features, the shocks and the estimator selection, and before $\theta$ and $T$, so it is uniform over $\Theta$; since $s(\theta)$ varies over $\Theta$, the factor $s$ is genuine. Remark 7's independence of $\tilde C$ from $d$ is not formalized ($d$ is part of the model). The estimate is any measurable maximizer of the integrated form of (17) (the paper's uniqueness claim is false in high dimension); the derivative bounds of endnote 2 are hypotheses; the support condition on continuous features is not formalized; the shocks are one fixed process for every $\theta$. Two hypotheses are added for each $\theta$: $s(\theta)\ge1$ (the paper's $s\in\{1,\dots,d+1\}$) and, almost surely, every realized demand lies in the closure of the range of $g$, which makes the estimate exist (it holds for the linear link and for binary demand under a logit link). Regret is a lower Lebesgue integral, so it cannot be made $0$ by non-integrability. The paper's proof is in its electronic companion.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), p. 5558, Theorem 3 and Remark 7

import Mathlib
import Definitions.Def_BanKeskin_UnknownSparsity_Model
import Definitions.Def_BanKeskin_UnknownSparsity_ILQX

namespace BanKeskin.UnknownSparsity

open MeasureTheory ProbabilityTheory

theorem theorem_3 {d : ℕ} (M : Model d) (c : ℝ) (hc : 0 < c)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (σ0 η0 : ℝ) (hS : M.Setting P Z ε σ0 η0)
    (est : (n : ℕ) → (Fin n → Feat d × ℝ × ℝ) → Param d) (hest : M.IsLassoMQLE c est) :
    ∃ C : ℝ, 0 < C ∧
      ∀ θ ∈ M.Theta, 0 < supportCard θ →
        (∀ᵐ ω ∂P, ∀ t, 1 ≤ t → M.demand Z ε est θ t ω ∈ closure (Set.range M.g)) →
        ∀ T : ℕ, 2 ≤ T →
          M.regret P Z ε est θ T ≤
            ENNReal.ofReal (C * supportCard θ * Real.sqrt T * (Real.log d + Real.log T)) := by sorry

end BanKeskin.UnknownSparsity
