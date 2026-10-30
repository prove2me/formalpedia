-- Prove2me | Theorems.Thm_CoVaRMC_Batching_order_stat_local_moments
-- name    : CoVaRMC.Batching.order_stat_local_moments
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-29T23:02:14.313207+00:00
-- url     : https://prove2.me/theorems/8b32b50a-c5d1-4d4d-820b-031233414f02
-- title:
--   Proof of Lemma 3, p. 10 — localized order-statistic bounds: Pr{|X_(⌈αm⌉)−VaR|>δ}, truncated bias and truncated second moment are O(m^{−1})
-- statement:
--   Let $(X_{0,j},Y_{0,j})$, $j=0,1,2,\dots$, be i.i.d. pairs with joint density $f$, marginal density $f_X(x)=\int f(x,y)\,dy$ and marginal distribution function $F_X$. For $m\ge1$ let $X_{(\lceil\alpha m\rceil)}$ be the $\lceil\alpha m\rceil$-th smallest of the first batch $X_{0,0},\dots,X_{0,m-1}$, where $\alpha\in(0,1)$. Let $v=\mathrm{VaR}_\alpha(X)$ satisfy $F_X(v)=\alpha$. Assume $f_X$ is continuously differentiable and strictly positive on an open set $\mathcal X\ni v$.
--
--   Then there exist $\delta>0$ and a constant $C$ such that, for all sufficiently large $m$,
--
--   1. $$\Pr\big\{|X_{(\lceil\alpha m\rceil)}-v|>\delta\big\}\le\frac Cm;$$
--   2. $$\Big|\mathbb E\Big[(X_{(\lceil\alpha m\rceil)}-v)\,I\{|X_{(\lceil\alpha m\rceil)}-v|\le\delta\}\Big]\Big|\le\frac Cm;$$
--   3. $$\mathbb E\Big[(X_{(\lceil\alpha m\rceil)}-v)^2\,I\{|X_{(\lceil\alpha m\rceil)}-v|\le\delta\}\Big]\le\frac Cm.$$
--
--   These are the order-statistic estimates behind Lemma 3 (the $O(m^{-1})$ within-batch error of the batching estimator). The source quotes them as $\mathbb E[X_{(\lceil\alpha m\rceil)}]-\mathrm{VaR}_\alpha(X)=O(m^{-1})$ and $\mathbb E|X_{(\lceil\alpha m\rceil)}-\mathrm{VaR}_\alpha(X)|^2=O(m^{-1})$ (Lemma 2 of Hong 2009). Here they are localized to a neighbourhood of $\mathrm{VaR}_\alpha(X)$, together with a tail bound. In this form they hold under the assumptions of Lemma 3 alone, with no moment condition on $X$. The untruncated moments can be infinite under those assumptions, e.g. when $1-F_X(x)\sim1/\log x$.
--
--   **Formalization Note.** The first batch is `S (0, j)`, `j < m`, and $X_{(\lceil\alpha m\rceil)}$ is `Xorder S α m 0`. The truncations are written with `Set.indicator` of the event $\{|X_{(\lceil\alpha m\rceil)}-v|\le\delta\}$, and "for all sufficiently large $m$" is `∀ᶠ m in atTop`.
-- source:
--   Huang, Lin, Hong, Monte-Carlo Estimation of CoVaR, arXiv:2210.06148v1, p. 10, proof of Lemma 3: the bounds E[X_(⌈αm⌉)] − VaR_α(X) = O(m^{-1}) and E|X_(⌈αm⌉) − VaR_α(X)|^2 = O(m^{-1}) quoted there from Lemma 2 of L. J. Hong (2009), Estimating quantile sensitivities, Operations Research 57(1):118–130; stated here localized to |X_(⌈αm⌉) − VaR_α(X)| ≤ δ together with the tail bound

import Mathlib
import Definitions.Def_CoVaRMC_Batching_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace CoVaRMC.Batching

theorem order_stat_local_moments (D : JointDensity) (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (v : ℝ) (𝒳 : Set ℝ) (h𝒳 : IsOpen 𝒳) (hv𝒳 : v ∈ 𝒳)
    (hfXc : ContDiffOn ℝ 1 D.fX 𝒳) (hfXpos : ∀ x ∈ 𝒳, 0 < D.fX x) (hv : D.FX v = α)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : ℕ × ℕ → Ω → ℝ × ℝ) (hSm : ∀ p, Measurable (S p)) (hSi : iIndepFun S P)
    (hSl : ∀ p, P.map (S p) = D.law) :
    ∃ δ > 0, ∃ C : ℝ, ∀ᶠ m : ℕ in atTop,
      (P {ω | δ < |Xorder S α m 0 ω - v|}).toReal ≤ C / m ∧
      |∫ ω, Set.indicator {ω | |Xorder S α m 0 ω - v| ≤ δ}
          (fun ω => Xorder S α m 0 ω - v) ω ∂P| ≤ C / m ∧
      ∫ ω, Set.indicator {ω | |Xorder S α m 0 ω - v| ≤ δ}
          (fun ω => (Xorder S α m 0 ω - v) ^ 2) ω ∂P ≤ C / m := by sorry

end CoVaRMC.Batching
