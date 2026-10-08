-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_rho_equal_iff
-- name    : CorreaThreshold.Adaptive.rho_equal_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:38.485696+00:00
-- url     : https://prove2.me/theorems/8f5a5901-fc8f-4e2c-934a-512ec4f31507
-- title:
--   §4 ‘Bounding γ₁’, p. 1463 — ρ₁ = ⋯ = ρₙ iff (n−1)/n((1 − ε_{i−1})ⁿ − (1 − εᵢ)ⁿ) = (1 − εᵢ)ⁿ⁻¹ − (1 − ε_{i+1})ⁿ⁻¹; γ₁ = 1 − x₁ⁿ⁻¹
-- statement:
--   Let $n\ge2$ and $0=\varepsilon_0<\varepsilon_1<\cdots<\varepsilon_n=1$, $A_i=[\varepsilon_{i-1},\varepsilon_i]$, $\psi(q)=(n-1)(1-q)^{n-2}$, $\gamma_i=\int_{A_i}\psi$, $\rho_1=1/\gamma_1$ and $\rho_{i+1}=(\rho_i/\gamma_{i+1})\int_{\varepsilon_{i-1}}^{\varepsilon_i}\psi(q)(1-q)\,dq$ for $i=1,\ldots,n-1$. Then all $\rho_i$ are equal if and only if
--   $$\int_{\varepsilon_i}^{\varepsilon_{i+1}}\psi(q)\,dq=\int_{\varepsilon_{i-1}}^{\varepsilon_i}\psi(q)(1-q)\,dq\qquad(i=1,\ldots,n-1),$$
--   if and only if
--   $$\frac{n-1}{n}\big((1-\varepsilon_{i-1})^n-(1-\varepsilon_i)^n\big)=(1-\varepsilon_i)^{n-1}-(1-\varepsilon_{i+1})^{n-1}\qquad(i=1,\ldots,n-1).$$
--   With $x_i=1-\varepsilon_i$ the last condition is the recursion (8), $x_{i-1}^n/n-x_i^n/n=x_i^{n-1}/(n-1)-x_{i+1}^{n-1}/(n-1)$ with $x_0=1$, $x_n=0$. Moreover $\gamma_1=\int_0^{\varepsilon_1}\psi(q)\,dq=1-x_1^{n-1}$.
--
--   This turns the choice of the partition into the Hill–Kertz recursion.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1463, §4 ‘Bounding γ₁’ (display before (8), and the sentence after (10))

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem rho_equal_iff {n : ℕ} (hn : 2 ≤ n) (ε : ℕ → ℝ) (hε0 : ε 0 = 0) (hεn : ε n = 1)
    (hεmono : ∀ i < n, ε i < ε (i + 1)) :
    ((∀ i ∈ Finset.Icc 1 n, rho n ε i = rho n ε 1) ↔
      ∀ i ∈ Finset.Icc 1 (n - 1), gam n ε (i + 1) = ∫ q in ε (i - 1)..ε i, psi n q * (1 - q)) ∧
    ((∀ i ∈ Finset.Icc 1 n, rho n ε i = rho n ε 1) ↔
      ∀ i ∈ Finset.Icc 1 (n - 1),
        ((n : ℝ) - 1) / n * ((1 - ε (i - 1)) ^ n - (1 - ε i) ^ n) =
          (1 - ε i) ^ (n - 1) - (1 - ε (i + 1)) ^ (n - 1)) ∧
    gam n ε 1 = 1 - (1 - ε 1) ^ (n - 1) := by sorry

end CorreaThreshold.Adaptive
