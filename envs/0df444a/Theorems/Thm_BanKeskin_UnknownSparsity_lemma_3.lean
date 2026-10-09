-- Prove2me | Theorems.Thm_BanKeskin_UnknownSparsity_lemma_3
-- name    : BanKeskin.UnknownSparsity.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:53.330983+00:00
-- url     : https://prove2.me/theorems/ba1b6c71-77b4-4b02-97e9-f1ca4466e8cc
-- title:
--   Lemma 3, p. 5558 — under ILQX, ‖θ̂^{lasso}_{t+1} − θ‖² ≤ ρ₃s(log d + log t)/√t with probability ≥ 1 − κ₃s(log d + log t)/√t
-- statement:
--   Consider the personalized pricing model of Ban and Keskin (2021) with link $g$, feature dimension $d\ge1$, parameter rectangle $\Theta\subset\mathbb R^{2(d+1)}$ and the standing assumptions on features and shocks. Fix $\tilde c>0$ and let $\pi = \mathrm{ILQX}(m_1,m_2,\lambda)$ with $\lambda_{t+1} = \tilde c\,t^{1/4}\sqrt{\log d+\log t}$, using any measurable selection $\hat\theta^{(\mathrm{lasso})}_{t+1}(\lambda_{t+1})$ of maximizers of the lasso quasi-likelihood objective (17).
--
--   Then there exist finite positive constants $\kappa_3,\rho_3,t_1$ such that for every $\theta\in\Theta$ with sparsity $s = s(\theta)$ and every $t\ge t_1$,
--
--   $$\mathbb P^\pi_{X,\theta}\Big\{\big\|\hat\theta^{(\mathrm{lasso})}_{t+1}(\lambda_{t+1})-\theta\big\|^2 \le \rho_3\,\frac{s(\log d+\log t)}{\sqrt t}\Big\} \ \ge\ 1-\kappa_3\,\frac{s(\log d+\log t)}{\sqrt t}, \qquad (20)$$
--
--   where $\|\cdot\|$ is the Euclidean norm and the estimate is the unprojected one, computed from the first $t$ periods.
--
--   This is the estimation-error rate on which Theorem 3 rests: the squared error scales with the sparsity $s$ and only logarithmically with the ambient dimension $d$.
--
--   **Formalization Note.** The constants are chosen after the model, the probability space, the features and shocks, and the estimator selection, and before $\theta$ and $t$; they do not depend on $\theta$ (hence not on $s$). Two hypotheses are added for each $\theta$: $s(\theta)\ge1$, as in the paper's "$s\in\{1,\dots,d+1\}$" (without it, $\theta=0$ would require the estimate to be exactly $0$ almost surely); and almost surely every realized demand lies in the closure of the range of $g$, which guarantees that (17) has a maximizer at the regularization levels used (the paper asserts existence without this; it holds for the linear link and for binary demand under a logit link). The probability is compared in $[0,\infty]$; a negative right-hand side is no claim. The log factor is $\log d + \log t > 0$ for $t\ge2$.
-- source:
--   Ban and Keskin, Personalized Dynamic Pricing with Machine Learning, Management Science 67(9) (2021), p. 5558, Lemma 3, (20)

import Mathlib
import Definitions.Def_BanKeskin_UnknownSparsity_Model
import Definitions.Def_BanKeskin_UnknownSparsity_ILQX

namespace BanKeskin.UnknownSparsity

open MeasureTheory ProbabilityTheory

theorem lemma_3 {d : ℕ} (M : Model d) (c : ℝ) (hc : 0 < c)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → Fin d → ℝ) (ε : ℕ → Ω → ℝ) (σ0 η0 : ℝ) (hS : M.Setting P Z ε σ0 η0)
    (est : (n : ℕ) → (Fin n → Feat d × ℝ × ℝ) → Param d) (hest : M.IsLassoMQLE c est) :
    ∃ κ3 ρ3 : ℝ, 0 < κ3 ∧ 0 < ρ3 ∧ ∃ t1 : ℕ, 0 < t1 ∧
      ∀ θ ∈ M.Theta, 0 < supportCard θ →
        (∀ᵐ ω ∂P, ∀ t, 1 ≤ t → M.demand Z ε est θ t ω ∈ closure (Set.range M.g)) →
        ∀ t : ℕ, t1 ≤ t →
          ENNReal.ofReal (1 - κ3 * supportCard θ * (Real.log d + Real.log t) / Real.sqrt t) ≤
            P {ω | sqNorm (est t (M.hist Z ε est θ t ω) - θ) ≤
              ρ3 * supportCard θ * (Real.log d + Real.log t) / Real.sqrt t} := by sorry

end BanKeskin.UnknownSparsity
