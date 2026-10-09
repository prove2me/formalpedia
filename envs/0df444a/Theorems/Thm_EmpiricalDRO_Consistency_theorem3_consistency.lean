-- Prove2me | Theorems.Thm_EmpiricalDRO_Consistency_theorem3_consistency
-- name    : EmpiricalDRO.Consistency.theorem3_consistency
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:07:06.64095+00:00
-- url     : https://prove2.me/theorems/87e70f64-12ef-4d26-8cb8-cd91409d4c22
-- title:
--   Theorem 3, p. 12 — Z_n(x) → Z0(x) and Z̄_n(x) → Z0(x) almost surely
-- statement:
--   Let $\xi_1,\xi_2,\dots$ be independent and identically distributed random elements of a measurable space $\Xi$, with law $P_0$. Fix a decision $x\in\mathbb R^m$ and a loss $h(x;\cdot):\Xi\to\mathbb R$, measurable, such that
--   $$
--   0<\mathrm{Var}_0(h(x;\xi))<\infty,\qquad Z_0(x)=E_0[h(x;\xi)]<\infty .
--   $$
--   Let $0<\alpha<1$ and let $\chi^2_{1,1-\alpha}$ be the $(1-\alpha)$-quantile of the $\chi^2_1$ distribution. For each $n$ let
--   $$
--   \underline Z_n(x)=\min_{w\in\mathcal U_n(\chi^2_{1,1-\alpha}/(2n))}\sum_{i=1}^n h(x;\xi_i)w_i,\qquad
--   \overline Z_n(x)=\max_{w\in\mathcal U_n(\chi^2_{1,1-\alpha}/(2n))}\sum_{i=1}^n h(x;\xi_i)w_i,
--   $$
--   where $\mathcal U_n(\eta)=\{w:-\frac1n\sum_i\log(nw_i)\le\eta,\ \sum_iw_i=1,\ w\ge0\}$ is the empirical Burg-entropy divergence ball (19). Then, almost surely,
--   $$
--   \underline Z_n(x)\to Z_0(x)\quad\text{and}\quad\overline Z_n(x)\to Z_0(x)\qquad(n\to\infty).
--   $$
--
--   Theorem 3 complements the coverage result Theorem 2: the empirical DRO bounds, calibrated with the $\chi^2_1$ quantile, not only bracket $Z_0(x)$ with asymptotic probability $1-\alpha$ but also shrink onto it.
--
--   **Formalization Note** The sample $\xi_1,\dots,\xi_n$ is `ξ 0, …, ξ (n-1)`. The moment conditions are `MemLp (h x ∘ ξ 0) 2` (finite mean and variance) and positive variance; the quantile $q=\chi^2_{1,1-\alpha}$ is pinned by $\mathcal N(0,1)\{y:y^2\le q\}=1-\alpha$. The paper's $\Theta$ only says where $x$ lives and is dropped. The positive variance and the value of $\alpha$ are kept as printed ("the same conditions in Theorem 2") although the conclusion does not need them. $\overline Z_n$ is the published `robustMean burg (q/2)` (ball radius $\rho/n$ with $\rho=q/2$), and $\underline Z_n$ is `robustLower burg (q/2)`.
-- source:
--   Lam, Recovering Best Statistical Guarantees via the Empirical DRO, arXiv:1605.09349v1, p. 12, Theorem 3 (conditions of Theorem 2, p. 11; (26)–(27), p. 11); proof p. 34

import Mathlib
import Definitions.Def_EmpiricalDRO_Consistency_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace EmpiricalDRO.Consistency

/-- Theorem 3, Lam, arXiv:1605.09349v1, p. 12: under the conditions of Theorem 2 (i.i.d. data,
`0 < Var₀(h(x;ξ)) < ∞`, `Z₀(x) = E₀[h(x;ξ)]` finite), for a fixed decision `x`, both empirical
DRO values `Z_n(x)` (min) and `Z̄_n(x)` (max) over the empirical Burg ball `U_n(χ²_{1,1−α}/(2n))`
converge almost surely to `Z₀(x)`. The sample `ξ_1, …, ξ_n` is `ξ 0, …, ξ (n-1)`, and `q` is the
`(1−α)`-quantile of `χ²₁` (the law of `Y²`, `Y ∼ N(0,1)`). -/
theorem theorem3_consistency {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Ξ : Type*} [MeasurableSpace Ξ]
    (ξ : ℕ → Ω → Ξ) (hξ : ∀ i, Measurable (ξ i)) (hindep : iIndepFun ξ P)
    (hident : ∀ i, IdentDistrib (ξ i) (ξ 0) P P)
    {m : ℕ} (h : EuclideanSpace ℝ (Fin m) → Ξ → ℝ) (x : EuclideanSpace ℝ (Fin m))
    (hhx : Measurable (h x))
    (hL2 : MemLp (fun ω => h x (ξ 0 ω)) 2 P)
    (hvar : 0 < variance (fun ω => h x (ξ 0 ω)) P)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (q : ℝ)
    (hq : gaussianReal 0 1 {y : ℝ | y ^ 2 ≤ q} = ENNReal.ofReal (1 - α)) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => EmpiricalDRO.Coverage.robustLower EmpiricalDRO.Coverage.burg (q / 2) (fun i : Fin n => h x (ξ i ω))) atTop
          (𝓝 (∫ ω', h x (ξ 0 ω') ∂P)) ∧
        Tendsto (fun n : ℕ =>
            GenEmpLik.Expansion.robustMean EmpiricalDRO.Coverage.burg (q / 2) (fun i : Fin n => h x (ξ i ω))) atTop
          (𝓝 (∫ ω', h x (ξ 0 ω') ∂P)) := by sorry

end EmpiricalDRO.Consistency
