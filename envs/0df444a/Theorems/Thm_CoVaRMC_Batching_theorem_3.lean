-- Prove2me | Theorems.Thm_CoVaRMC_Batching_theorem_3
-- name    : CoVaRMC.Batching.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:09:04.584111+00:00
-- url     : https://prove2.me/theorems/02082189-8682-494e-9054-d17d40d89638
-- title:
--   Theorem 3, p. 11 — Ŷ^BE − CoVaR = O_Pr(n^{−1/3}) when √k/m → c ≠ 0, and √k(Ŷ^BE − CoVaR) is asymptotically normal when √k/m → 0
-- statement:
--   Let $(X, Y)$ have a joint density $f$ with marginal density $f_X$ and conditional distribution function $F_{Y|X}$ (Equation (3)), let $\alpha, \beta \in (0,1)$, and let $\mathrm{VaR}_\alpha(X)$ and $\mathrm{CoVaR}_{\alpha,\beta}$ satisfy
--   $$\Pr\{X \le \mathrm{VaR}_\alpha(X)\} = \alpha, \qquad \Pr\{Y \le \mathrm{CoVaR}_{\alpha,\beta} \mid X = \mathrm{VaR}_\alpha(X)\} = \beta.$$
--   Suppose Assumption 1 holds and there is $M > 0$ with $|\frac{\partial}{\partial x}F_{Y|X}(y\mid \mathrm{VaR}_\alpha(X))| \le M$ for all $y \in \mathcal Y$ and $|\frac{\partial^2}{\partial x^2}F_{Y|X}(y\mid x)| \le M$ for all $(x, y) \in \mathbb R \times \mathcal Y$. From an i.i.d. sample of size $n = k \times m$ form the batching estimator $\hat Y^{\mathrm{BE}}$ with $k$ batches of $m$ observations, and let $k \to \infty$ and $m \to \infty$ as $n \to \infty$.
--
--   1. When $\sqrt k/m \to c$ for some constant $c \ne 0$,
--   $$\hat Y^{\mathrm{BE}} - \mathrm{CoVaR}_{\alpha,\beta} = O_{\Pr}\big(n^{-1/3}\big).$$
--   2. When $\sqrt k/m \to 0$,
--   $$\sqrt k\,\big(\hat Y^{\mathrm{BE}} - \mathrm{CoVaR}_{\alpha,\beta}\big) \Rightarrow \frac{\sqrt{\beta(1-\beta)}}{f_{Y|X}(\mathrm{CoVaR}_{\alpha,\beta}\mid \mathrm{VaR}_\alpha(X))}\cdot N(0,1).$$
--
--   The theorem identifies $n^{-1/3}$ as the optimal rate of the batching estimator, slower than the $n^{-1/2}$ of ordinary quantile estimators because the conditioning event $\{X = \mathrm{VaR}_\alpha(X)\}$ has probability zero and $\mathrm{VaR}_\alpha(X)$ must itself be estimated; in the regime $\sqrt k/m \to 0$ the limit is the one obtained as if $\mathrm{VaR}_\alpha(X)$ were known.
--
--   **Formalization Note.** $k$ and $m$ are sequences $k(\nu), m(\nu) \ge 1$ tending to infinity, with $n = k(\nu)m(\nu)$; the paper's case $k(n)m(n) = n$ is $\nu = n$. Batches are nonempty ($k, m \ge 1$, added). $O_{\Pr}$ is the definition of p. 5: for every $\varepsilon > 0$ one constant $C > 0$ works for all $\nu$. "$\Rightarrow$" is convergence in distribution (`TendstoInDistribution`) to the centred normal law with variance $\beta(1-\beta)/f_{Y|X}(\mathrm{CoVaR}_{\alpha,\beta}\mid\mathrm{VaR}_\alpha(X))^2$, where $f_{Y|X}(y\mid x) = f(x,y)/f_X(x)$; this variance is positive under Assumption 1, so its conversion to a nonnegative real loses nothing. $F_{Y|X}$ is a version agreeing with (3) wherever $f_X > 0$, and $\mathrm{VaR}_\alpha(X)$, $\mathrm{CoVaR}_{\alpha,\beta}$ enter as reals satisfying (1) and (2).
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 11, Theorem 3

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

/-- Theorem 3, p. 11: with `k → ∞`, `m → ∞` and `n = k m`, (a) if `√k/m → c₀ ≠ 0` then
`Ŷ^BE - CoVaR_{α,β} = O_Pr(n^{-1/3})`; (b) if `√k/m → 0` then
`√k (Ŷ^BE - CoVaR_{α,β}) ⇒ (√(β(1-β)) / f_{Y|X}(CoVaR_{α,β} | VaR_α(X))) · N(0, 1)`. -/
theorem theorem_3 (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law)
    (k m : ℕ → ℕ) (hk0 : ∀ ν, 0 < k ν) (hm0 : ∀ ν, 0 < m ν)
    (hk : Tendsto k atTop atTop) (hm : Tendsto m atTop atTop) :
    (∀ c0 : ℝ, c0 ≠ 0 → Tendsto (fun ν => √(k ν : ℝ) / m ν) atTop (𝓝 c0) →
      OPr P (fun ν ω => YBE S α β (k ν) (m ν) ω - c)
        (fun ν => ((k ν * m ν : ℕ) : ℝ) ^ (-(1 / 3 : ℝ)))) ∧
    (Tendsto (fun ν => √(k ν : ℝ) / m ν) atTop (𝓝 0) →
      TendstoInDistribution (fun ν ω => √(k ν : ℝ) * (YBE S α β (k ν) (m ν) ω - c)) atTop id
        (fun _ => P) (gaussianReal 0 (β * (1 - β) / D.condDensity c v ^ 2).toNNReal)) := by sorry

end CoVaRMC.Batching
