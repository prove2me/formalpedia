-- Prove2me | Theorems.Thm_CoVaRMC_Batching_lemma_3
-- name    : CoVaRMC.Batching.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:08:46.402126+00:00
-- url     : https://prove2.me/theorems/3b43e3e1-ab3e-4b05-8b9d-169663c6a606
-- title:
--   Lemma 3, p. 10 — sup_{y∈𝒴} |E[I{Ŷ ≤ y}] − F_{Y|X}(y | VaRα(X))| = O(m^{−1})
-- statement:
--   Let $(X_{i,j}, Y_{i,j})$ be i.i.d. with joint density $f$, let $\alpha, \beta \in (0,1)$, and let $v = \mathrm{VaR}_\alpha(X)$ and $c = \mathrm{CoVaR}_{\alpha,\beta}$, i.e. $F_X(v) = \alpha$ and $F_{Y|X}(c\mid v) = \beta$. Suppose Assumption 1 holds and there is $M > 0$ such that
--   $$\Big|\frac{\partial}{\partial x}F_{Y|X}(y\mid \mathrm{VaR}_\alpha(X))\Big| \le M \ \text{ for all } y \in \mathcal Y, \qquad \Big|\frac{\partial^2}{\partial x^2}F_{Y|X}(y\mid x)\Big| \le M \ \text{ for all } (x,y) \in \mathbb R \times \mathcal Y.$$
--   Then, with $\hat Y$ the concomitant of the $\lceil \alpha m\rceil$-th order statistic in a batch of size $m$, there is a constant $C$ such that for all sufficiently large $m$,
--   $$\sup_{y \in \mathcal Y}\Big|\mathrm E\big[I\{\hat Y \le y\}\big] - F_{Y|X}\big(y \mid \mathrm{VaR}_\alpha(X)\big)\Big| \le \frac{C}{m},$$
--   that is, the within-batch error is $O(m^{-1})$ uniformly on $\mathcal Y$ as $m \to \infty$.
--
--   This is the bias half of the error decomposition (5); it fixes the rate at which $m$ must grow relative to $\sqrt k$ in Theorem 3.
--
--   **Formalization Note.** $F_{Y|X}$ is a version $F_c$ agreeing with (3) where $f_X > 0$, and $\partial/\partial x$ is the derivative in the second argument of $F_c$. "$\sup \le C/m$" is written as "every term $\le C/m$". No moment or tail condition on $(X, Y)$ is assumed.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 10, Lemma 3

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

/-- Lemma 3, p. 10: under Assumption 1 and the derivative bounds `M`,
`sup_{y ∈ 𝒴} |E[I{Ŷ ≤ y}] - F_{Y|X}(y | VaR_α(X))| = O(m^{-1})` as `m → ∞`. -/
theorem lemma_3 (D : JointDensity) (Fc : ℝ → ℝ → ℝ) (α β : ℝ)
    (hα : α ∈ Set.Ioo (0 : ℝ) 1) (hβ : β ∈ Set.Ioo (0 : ℝ) 1)
    (v c : ℝ) (𝒳 𝒴 : Set ℝ) (hFc : IsCondCDFVersion D Fc) (hA1 : Assumption1 D Fc v c 𝒳 𝒴)
    (hv : D.FX v = α) (hc : Fc c v = β)
    (M : ℝ) (hM : 0 < M)
    (hM1 : ∀ y ∈ 𝒴, |deriv (fun x => Fc y x) v| ≤ M)
    (hM2 : ∀ x : ℝ, ∀ y ∈ 𝒴, |deriv (deriv (fun x => Fc y x)) x| ≤ M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law) :
    ∃ C : ℝ, ∀ᶠ m : ℕ in atTop, ∀ y ∈ 𝒴, |pHat P S α m y - Fc y v| ≤ C / m := by sorry

end CoVaRMC.Batching
