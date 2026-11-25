-- Prove2me | Theorems.Thm_Arxiv1706_02824_sinc_squared_delta_limit
-- name    : Arxiv1706_02824.sinc_squared_delta_limit
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T00:45:01.400895+00:00
-- url     : https://prove2.me/theorems/a6731f36-393c-450d-9892-4b5da1e2fccc
-- title:
--   Eqs. (A10)-(A11): $T\,\mathrm{sinc}^2(\pi\nu T)$ tends to $\delta(\nu)$
-- statement:
--   Let $f_T(\nu)=\sin^2(\pi\nu T)/(\pi^2\nu^2T)$, with $f_T(0)=T$, so that $\mathrm{sinc}^2(\pi\nu T)=f_T(\nu)/T$. Then:
--
--   1. (A10) $f_T(0)\to\infty$ as $T\to\infty$, and $f_T(\nu)\to0$ as $T\to\infty$ for every fixed $\nu\ne0$.
--   2. (A11) For every $T>0$,
--   $$\int_{-\infty}^{\infty}f_T(\nu)\,d\nu=1.$$
--   3. $f_T\to\delta$ as $T\to\infty$: $\int f_T(\nu)g(\nu)\,d\nu\to g(0)$ for every smooth compactly supported $g$.
--   4. For every fixed $\nu$, $\mathrm{sinc}^2(\pi\nu T)\to1$ as $T\to0$.
--
--   These limits justify the approximations $\mathrm{sinc}^2[\pi\nu T]\cong\delta(\nu)/T$ for long exposures and $\mathrm{sinc}^2[\pi\nu T]\cong1$ for short ones.
--
--   **Formalization Note** The test functions $g$ are complex-valued. The statement (A11) requires $T>0$, which the paper leaves implicit; for $T\le0$ the integral is $0$ or $-1$.
-- source:
--   Gureyev, Kozlov, Paganin, Nesterets, de Hoog and Quiney, On the van Cittert - Zernike theorem for intensity correlations and its applications, arXiv:1706.02824v1 (2017), claim c028; Appendix, eqs. (A10)-(A11) and the limit sinc^2[pi nu T] ≅ (1/T) delta(nu), PDF p. 8

import Mathlib
import Definitions.Def_Arxiv1706_02824_Basic

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped ComplexConjugate

namespace Arxiv1706_02824

theorem sinc_squared_delta_limit :
    Tendsto (fun T : ℝ => fejerKernelT T 0) atTop atTop ∧
    (∀ ν : ℝ, ν ≠ 0 → Tendsto (fun T : ℝ => fejerKernelT T ν) atTop (𝓝 0)) ∧
    (∀ T : ℝ, 0 < T → ∫ ν : ℝ, fejerKernelT T ν = 1) ∧
    (∀ g : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      Tendsto (fun T : ℝ => ∫ ν : ℝ, (fejerKernelT T ν : ℂ) * g ν) atTop (𝓝 (g 0))) ∧
    (∀ ν : ℝ, Tendsto (fun T : ℝ => Real.sinc (π * ν * T) ^ 2) (𝓝 0) (𝓝 1)) := by sorry

end Arxiv1706_02824
