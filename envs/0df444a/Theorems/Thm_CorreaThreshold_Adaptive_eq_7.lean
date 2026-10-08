-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_eq_7
-- name    : CorreaThreshold.Adaptive.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:27.231409+00:00
-- url     : https://prove2.me/theorems/29773f0d-e6cb-4e91-b510-cfd1d1db7312
-- title:
--   (7), p. 1461 — E(max Xᵢ) = ∫₀^∞ 1 − Fⁿ = ∫₀¹ F⁻¹(ⁿ√z) dz = n∫₀¹(1 − q)ⁿ⁻¹F⁻¹(1 − q) dq = n∫₀¹ψ(q)R(q) dq
-- statement:
--   Throughout, $X_1,\ldots,X_n$ are i.i.d. with common law $\mu$ on $\mathbb R$, where $\mu$ is a probability measure with $\mu((-\infty,0))=0$ (the variables are nonnegative), and $F(x)=\mu((-\infty,x])$ is their distribution function. Let $n\ge2$, $\psi(q)=(n-1)(1-q)^{n-2}$ and $R(q)=\int_0^qF^{-1}(1-\theta)\,d\theta$. Then
--   $$E(\max\{X_1,\ldots,X_n\})=\int_0^\infty 1-F^n(t)\,dt=\int_0^1F^{-1}(\sqrt[n]{z})\,dz=n\int_0^1(1-q)^{n-1}F^{-1}(1-q)\,dq=n\int_0^1(n-1)(1-q)^{n-2}R(q)\,dq.$$
--
--   The last form expresses the prophet's value as a $\psi$-weighted average of $R$, which is the shape the quantile rule is designed to reproduce.
--
--   **Formalization Note** All quantities are in $[0,\infty]$ (lower Lebesgue integrals), so the identity also covers $E X=\infty$. The first three equalities hold for $n\ge1$; the last uses $(1-q)^{n-1}=0$ at $q=1$ and is stated for $n\ge2$, the range of §4 (for $n=1$, $\psi\equiv0$). The integrals over $[0,1]$ are taken over the open interval $(0,1)$, which avoids the junk value of $F^{-1}(1)$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1461, (7)

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem eq_7 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) :
    SamuelCahnProphet.IID.Emax μ n = ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (1 - cdf μ t ^ n) ∧
      SamuelCahnProphet.IID.Emax μ n =
        ∫⁻ z in Set.Ioo 0 1, ENNReal.ofReal (Finv μ (z ^ ((1 : ℝ) / n))) ∧
      SamuelCahnProphet.IID.Emax μ n =
        ∫⁻ q in Set.Ioo 0 1, ENNReal.ofReal (n * (1 - q) ^ (n - 1)) * ENNReal.ofReal (Finv μ (1 - q)) ∧
      SamuelCahnProphet.IID.Emax μ n =
        ∫⁻ q in Set.Ioo 0 1, ENNReal.ofReal (n * psi n q) * Rq μ q := by sorry

end CorreaThreshold.Adaptive
