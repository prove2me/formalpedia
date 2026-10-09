-- Prove2me | Theorems.Thm_EmpiricalDRO_Coverage_theorem2_coverage
-- name    : EmpiricalDRO.Coverage.theorem2_coverage
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T15:09:23.410362+00:00
-- url     : https://prove2.me/theorems/d7f7fbfc-1576-46de-9ab5-5ff46bb6c5f8
-- title:
--   Theorem 2, p. 11 — lim_n P(Z_n(x) ≤ Z0(x) ≤ Z̄_n(x)) = 1 − α for the empirical Burg ball of radius χ²_{1,1−α}/(2n)
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be i.i.d. random elements of a measurable space $\Xi$ under a probability measure $P_0$, let $h(x;\cdot):\Xi\to\mathbb R$ be measurable for a fixed decision $x\in\mathbb R^m$, and assume
--   $$
--   0<\operatorname{Var}_0\big(h(x;\xi)\big)<\infty,\qquad Z_0(x)=\mathbb E_0[h(x;\xi)]<\infty .
--   $$
--   Fix $\alpha\in(0,1)$ and let $\chi^2_{1,1-\alpha}$ be the $(1-\alpha)$-quantile of the $\chi^2_1$ distribution. Define the empirical DRO bounds
--   $$
--   \underline Z_n(x)=\min_{w\in\mathcal U_n(\chi^2_{1,1-\alpha}/(2n))}\sum_{i=1}^n h(x;\xi_i)w_i,\qquad
--   \overline Z_n(x)=\max_{w\in\mathcal U_n(\chi^2_{1,1-\alpha}/(2n))}\sum_{i=1}^n h(x;\xi_i)w_i,
--   $$
--   where $\mathcal U_n(\eta)=\{w:\ -\frac1n\sum_i\log(nw_i)\le\eta,\ \sum_i w_i=1,\ w\ge0\}$ is the empirical Burg-entropy divergence ball. Then
--   $$
--   \lim_{n\to\infty}P\big(\underline Z_n(x)\le Z_0(x)\le\overline Z_n(x)\big)=1-\alpha .
--   $$
--
--   The empirical DRO with a Burg ball of radius $\chi^2_{1,1-\alpha}/(2n)$ therefore yields an asymptotically exact $(1-\alpha)$ two-sided confidence interval for the expected loss $Z_0(x)$, with one degree of freedom whatever the support of $\xi$.
--
--   **Formalization Note.** The sample is $\xi_0,\dots,\xi_{n-1}$ in Lean (0-based). The moment assumption is $h(x;\xi)\in L^2(P_0)$ together with positive variance. The quantile $q=\chi^2_{1,1-\alpha}$ is characterized by $P(Y^2\le q)=1-\alpha$ for $Y\sim N(0,1)$, which determines $q$ uniquely. The minimum and maximum are the infimum `robustLower burg (q/2)` and the published supremum `robustMean burg (q/2)` (ball radius $(q/2)/n$). The paper fixes $x\in\Theta\subset\mathbb R^m$; the set $\Theta$ plays no role in a pointwise statement and is dropped, so $x$ is arbitrary. The probability of the event is an outer probability; no measurability is assumed (the paper sets measurability aside, p. 14).
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 11, Theorem 2, (25)–(27); proof p. 23

import Mathlib
import Definitions.Def_EmpiricalDRO_Coverage_Setting
open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Coverage

/-- Theorem 2, Lam, arXiv:1605.09349v1, p. 11: for a fixed decision `x`, i.i.d. data and
`0 < Var h(x;ξ) < ∞`, `P(Z_n(x) ≤ Z0(x) ≤ Z̄_n(x)) → 1 − α`, where `Z_n(x)` and `Z̄_n(x)` are the
minimum and maximum of `∑ wᵢ h(x;ξᵢ)` over the empirical Burg ball `U_n(χ²_{1,1−α}/(2n))` and
`q = χ²_{1,1−α}` is pinned by `P(N(0,1)² ≤ q) = 1 − α`. -/
theorem theorem2_coverage {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ξ : Type*} [MeasurableSpace Ξ] (ξ : ℕ → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i))
    (hindep : iIndepFun ξ P) (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → Ξ → ℝ) (x : EuclideanSpace ℝ (Fin m))
    (hhx : Measurable (h x)) (hL2 : MemLp (fun ω => h x (ξ 0 ω)) 2 P)
    (hvar : 0 < variance (fun ω => h x (ξ 0 ω)) P)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (q : ℝ)
    (hq : gaussianReal 0 1 {y : ℝ | y ^ 2 ≤ q} = ENNReal.ofReal (1 - α)) :
    Tendsto (fun n : ℕ => P {ω |
      robustLower burg (q / 2) (fun i : Fin n => h x (ξ i ω)) ≤ ∫ ω', h x (ξ 0 ω') ∂P ∧
        ∫ ω', h x (ξ 0 ω') ∂P ≤
          GenEmpLik.Expansion.robustMean burg (q / 2) (fun i : Fin n => h x (ξ i ω))})
      atTop (𝓝 (ENNReal.ofReal (1 - α))) := by sorry

end EmpiricalDRO.Coverage
