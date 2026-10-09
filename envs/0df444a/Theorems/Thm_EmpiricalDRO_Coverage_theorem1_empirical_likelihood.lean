-- Prove2me | Theorems.Thm_EmpiricalDRO_Coverage_theorem1_empirical_likelihood
-- name    : EmpiricalDRO.Coverage.theorem1_empirical_likelihood
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:21.95239+00:00
-- url     : https://prove2.me/theorems/51b9150e-a9b9-4edb-b02b-29e4b792b8ab
-- title:
--   Theorem 1 (Owen 1988), p. 10 — −2 log R(μ₀) ⇒ χ²₁ as n → ∞
-- statement:
--   **The empirical likelihood theorem.** Let $\xi_1,\xi_2,\dots$ be i.i.d. random elements of a measurable space $\Xi$ under a probability measure $P$, and let $g:\Xi\to\mathbb R$ be measurable with $\mathbb E\,g(\xi)^2<\infty$ and $0<\operatorname{Var}g(\xi)$. Let $\mu_0=\mathbb E\,g(\xi)$, and let
--   $$
--   -2\log R(\mu_0)=\inf\Big\{-2\sum_{i=1}^n\log(nw_i):\ w_i>0,\ \sum_i w_i=1,\ \sum_i w_ig(\xi_i)=\mu_0\Big\},
--   $$
--   defined as $+\infty$ if no weight vector is feasible. Then
--   $$
--   -2\log R(\mu_0)\Rightarrow\chi^2_1\qquad(n\to\infty),
--   $$
--   i.e. for every $t\in\mathbb R$,
--   $$
--   P\big(-2\log R(\mu_0)\le t\big)\longrightarrow P(Y^2\le t),\qquad Y\sim N(0,1).
--   $$
--
--   This is the nonparametric analogue of Wilks' theorem: the profile empirical likelihood ratio for a mean is asymptotically $\chi^2_1$, which calibrates the empirical DRO with radius $\chi^2_{1,1-\alpha}/(2n)$.
--
--   **Formalization Note.** Convergence in distribution to $\chi^2_1$ is stated as convergence of the distribution function at every $t$; this is equivalent because the $\chi^2_1$ distribution function is continuous. The statistic takes values in $[0,+\infty]$ and the value $+\infty$ never satisfies "$\le t$". The moment assumption "$\mu_0<\infty$ and $0<\operatorname{Var}<\infty$" is encoded as $g(\xi)\in L^2$ together with positive variance. Probabilities of events are outer probabilities. The sample is indexed from $0$.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 10, Theorem 1 (Owen (1988)), (22)–(23)

import Mathlib
import Definitions.Def_EmpiricalDRO_Coverage_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Coverage

/-- Theorem 1 (the empirical likelihood theorem, Owen (1988)), Lam, arXiv:1605.09349v1, p. 10:
for i.i.d. data and `g` with `0 < Var g(ξ) < ∞`, `−2 log R(μ₀) ⇒ χ²₁`, stated as convergence of the
distribution function at every `t` (the χ²₁ distribution function is continuous). The statistic is
`⊤` when (22) is infeasible. -/
theorem theorem1_empirical_likelihood {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Ξ : Type*} [MeasurableSpace Ξ] (ξ : ℕ → Ω → Ξ)
    (hξ : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    (g : Ξ → ℝ) (hg : Measurable g) (hL2 : MemLp (fun ω => g (ξ 0 ω)) 2 P)
    (hvar : 0 < variance (fun ω => g (ξ 0 ω)) P) :
    ∀ t : ℝ, Tendsto (fun n : ℕ =>
      P {ω | elStat (fun i : Fin n => g (ξ i ω)) (∫ ω', g (ξ 0 ω') ∂P) ≤ (t : EReal)})
      atTop (𝓝 (gaussianReal 0 1 {y : ℝ | y ^ 2 ≤ t})) := by sorry

end EmpiricalDRO.Coverage
