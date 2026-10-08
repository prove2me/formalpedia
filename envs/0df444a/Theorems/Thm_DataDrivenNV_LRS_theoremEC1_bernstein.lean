-- Prove2me | Theorems.Thm_DataDrivenNV_LRS_theoremEC1_bernstein
-- name    : DataDrivenNV.LRS.theoremEC1_bernstein
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:25:09.187268+00:00
-- url     : https://prove2.me/theorems/c680c772-6a31-486e-acf8-8a21ce07dab2
-- title:
--   Theorem EC.1 (Bernstein), p. ec5 — Pr((1/N)ΣXⁱ − E X¹ ≥ t) ≤ exp(−Nt²/(2σ² + 2tc/3))
-- statement:
--   **Bernstein's inequality.** Let $X^1,\dots,X^N$ ($N\ge1$) be i.i.d. real random variables with common law $\nu$ such that $|X^1|\le c$ and $|X^1-\mathbb E[X^1]|\le c$ almost surely, and $\operatorname{Var}(X^1)=\sigma^2$. Then for every $t>0$,
--   $$\Pr\Big(\frac1N\sum_{i=1}^N X^i - \mathbb E[X^1] \ge t\Big) \le \exp\Big(\frac{-Nt^2}{2\sigma^2 + 2tc/3}\Big).$$
--
--   In the paper this is applied to indicators $X^i=\mathbf 1[D^i\le q]$ (with $c=1$ and $\sigma^2=F(q)(1-F(q))$) to bound how far the empirical cdf can overshoot the true cdf, which is the step (EC.2) of the proof of Proposition EC.1.
--
--   **Formalization Note** The i.i.d. sample is the coordinate process of the product measure $\nu^{\otimes N}$ on $\mathbb R^N$. The paper prints only $|X^1|\le c$; the centred bound $|X^1-\mathbb E X^1|\le c$ is added because this form of Bernstein's inequality is the standard one for centred bounded variables (with only $|X^1|\le c$ the centred variable can reach $2c$). The printed form is false without it: for $X^1\in\{-1,1\}$ with $\Pr(X^1=1)=0.01$, $c=1$, $t=0.2$ and $N=500$, the exact binomial tail is about $1.2\cdot10^{-38}$ while the printed bound is about $1.4\cdot10^{-41}$. Both bounds hold for the indicators to which the paper applies the inequality, so every use in the paper is covered.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. ec5, Theorem EC.1 (Bernstein 1927)

import Mathlib
import Definitions.Def_DataDrivenNV_LRS_Setting

open MeasureTheory ProbabilityTheory

namespace DataDrivenNV.LRS

/-- Theorem EC.1 (Bernstein's inequality), p. ec5. Let `X¹, …, Xᴺ` be i.i.d. with law `ν`
(the coordinates of the product measure `ν^⊗N`), with `|X¹| ≤ c` and `|X¹ - E X¹| ≤ c` almost
surely and `Var(X¹) = σ²`. Then for every `t > 0`,
`Pr((1/N) Σᵢ Xⁱ - E X¹ ≥ t) ≤ exp(-N t² / (2σ² + 2tc/3))`.
The centred bound `hcent` is added to the printed hypothesis `|X¹| ≤ c`; it holds in every use
the paper makes of the inequality (indicators, `c = 1`). -/
theorem theoremEC1_bernstein (ν : Measure ℝ) [IsProbabilityMeasure ν] (N : ℕ) (hN : 1 ≤ N)
    (c σ : ℝ) (hc : ∀ᵐ x ∂ν, |x| ≤ c) (hcent : ∀ᵐ x ∂ν, |x - ∫ y, y ∂ν| ≤ c)
    (hvar : ∫ x, (x - ∫ y, y ∂ν) ^ 2 ∂ν = σ ^ 2) (t : ℝ) (ht : 0 < t) :
    (Measure.pi fun _ : Fin N => ν)
        {x : Fin N → ℝ | t ≤ (1 / (N : ℝ)) * ∑ i, x i - ∫ y, y ∂ν} ≤
      ENNReal.ofReal (Real.exp (-((N : ℝ) * t ^ 2) / (2 * σ ^ 2 + 2 * t * c / 3))) := by sorry

end DataDrivenNV.LRS
