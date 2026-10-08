-- Prove2me | Theorems.Thm_DataDrivenNV_WMS_proposition1_extremal_density
-- name    : DataDrivenNV.WMS.proposition1_extremal_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:36:13.717989+00:00
-- url     : https://prove2.me/theorems/5180fe91-44a7-48e3-842f-80ca6078001c
-- title:
--   Proposition 1, p. 15 — the truncated exponential f̃ of (12) has the smallest AMS in L_{q,γ₀,γ₁} (case γ₁ ≠ 0, open range)
-- statement:
--   Let $b,h,\gamma_0>0$, $q\in\mathbb R$ and $\gamma_1\neq0$ with
--   $$-\frac{b+h}{h}<\frac{\gamma_1}{\gamma_0}<\frac{b+h}{b}.$$
--   Let $\mathbb L_{q,\gamma_0,\gamma_1}$ be the set of log-concave probability densities $f$ with $b/(b+h)$ quantile $q$, $f(q)=\gamma_0$ and $\gamma_1\in\partial\log f(q)$. Let $\tilde f(x)=\gamma_0e^{\gamma_1(x-q)}$ on $[\underline x,\overline x]$ and $0$ elsewhere, where $\underline x=q+\frac1{\gamma_1}\log\big(1-\frac{\gamma_1}{\gamma_0}\frac{b}{b+h}\big)$ and $\overline x=q+\frac1{\gamma_1}\log\big(1+\frac{\gamma_1}{\gamma_0}\frac{h}{b+h}\big)$ (display (12)). Then:
--
--   1. $\tilde f\in\mathbb L_{q,\gamma_0,\gamma_1}$: it is a log-concave probability density, its $b/(b+h)$ quantile is $q$, $\tilde f(q)=\gamma_0$ and $\gamma_1\in\partial\log\tilde f(q)$;
--   2. $\tilde f$ has the smallest absolute mean spread at $q$ in the class:
--   $$\Delta_{\tilde f}(q)\ \le\ \Delta_f(q)\qquad\text{for every } f\in\mathbb L_{q,\gamma_0,\gamma_1}.$$
--
--   This solves the constrained problem (11) in closed form and is the main step towards the uniform lower bound of Proposition 2.
--
--   **Formalization Note** The statement covers the case $\gamma_1\neq0$ with $\gamma_1/\gamma_0$ strictly inside the range of Lemma 1. At $\gamma_1=0$ the printed endpoints divide by zero (the minimizer is then a uniform density), and at $\gamma_1/\gamma_0=(b+h)/b$ or $-(b+h)/h$ one endpoint is infinite (a one-sided exponential density); these cases are not covered by (12) as written. No integrability hypothesis is placed on $f$: a log-concave density has exponential tails, so the conditional means exist.
-- source:
--   Levi, Perakis & Uichanco, The Data-Driven Newsvendor Problem: New Bounds and Insights, authors' accepted manuscript (MIT DSpace), p. 15, Proposition 1 and (12); proof p. 15

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_DataDrivenNV_WMS_Setting

namespace DataDrivenNV.WMS

open MeasureTheory

/-- **Proposition 1** (p. 15), case `γ₁ ≠ 0`, `−(b+h)/h < γ₁/γ₀ < (b+h)/b`: the density
`f̃ = γ₀ e^{γ₁(x−q)}` on `[x̲, x̄]` of (12) belongs to `L_{q,γ₀,γ₁}` (log-concave pdf with
`b/(b+h)` quantile `q`, `f̃(q) = γ₀`, `γ₁ ∈ ∂ log f̃(q)`), and has the smallest AMS at `q`
among all members of `L_{q,γ₀,γ₁}`. -/
theorem proposition1_extremal_density (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (q γ₀ γ₁ : ℝ) (hγ₀ : 0 < γ₀) (hγ₁ : γ₁ ≠ 0)
    (hlo : -((b + h) / h) < γ₁ / γ₀) (hhi : γ₁ / γ₀ < (b + h) / b) :
    (IsPdf (tildeF b h q γ₀ γ₁) ∧
      ConvexOptimization.LogConcaveOn Set.univ (tildeF b h q γ₀ γ₁) ∧
      quantileOf (tildeF b h q γ₀ γ₁) (b / (b + h)) = q ∧
      tildeF b h q γ₀ γ₁ q = γ₀ ∧
      IsLogSupergradient (tildeF b h q γ₀ γ₁) q γ₁) ∧
    ∀ f : ℝ → ℝ, IsPdf f → ConvexOptimization.LogConcaveOn Set.univ f →
      quantileOf f (b / (b + h)) = q → f q = γ₀ → IsLogSupergradient f q γ₁ →
      ams (tildeF b h q γ₀ γ₁) q ≤ ams f q := by sorry

end DataDrivenNV.WMS
