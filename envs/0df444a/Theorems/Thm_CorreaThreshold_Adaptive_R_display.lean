-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_R_display
-- name    : CorreaThreshold.Adaptive.R_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:37.066983+00:00
-- url     : https://prove2.me/theorems/db663dad-465b-48e5-97c4-246c4f3c45d0
-- title:
--   §4, p. 1462 — the quantile rule accepts with probability q and its expected reward is R(q) = qτ(q) + ∫_{τ(q)}^∞ 1 − F(t) dt
-- statement:
--   Throughout, $X_1,\ldots,X_n$ are i.i.d. with common law $\mu$ on $\mathbb R$, where $\mu$ is a probability measure with $\mu((-\infty,0))=0$ (the variables are nonnegative), and $F(x)=\mu((-\infty,x])$ is their distribution function. Fix $q\in(0,1]$ and $\tau(q)=F^{-1}(1-q)$. Let $U$ be uniform on $[0,1]$ and independent of $X$, and stop on $X$ when $X>\tau(q)$, or when $X=\tau(q)$ and $U\le s$, where $s=[q-P(X>\tau(q))]/P(X=\tau(q))$. Then the rule accepts with probability $q$, and
--   $$E[X\,\mathbf 1\{\text{stop}\}]=P(X=\tau(q))\,s\,\tau(q)+P(X>\tau(q))E[X\mid X>\tau(q)]=q\tau(q)+\int_{\tau(q)}^\infty1-F(t)\,dt=\int_0^qF^{-1}(1-\theta)\,d\theta=R(q).$$
--
--   This is the single-step identity behind the whole analysis: an acceptance probability $q$ yields expected reward $R(q)$.
--
--   **Formalization Note** The statement has three parts: the acceptance probability is $q$; the expected stopped reward equals $R(q)$; and $q\tau(q)+\int_{\tau(q)}^\infty(1-F)=R(q)$. Expectations are in $[0,\infty]$. When $P(X=\tau(q))=0$, Lean's $s$ equals $0$ and the coin only matters on a null event.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1462, §4 (display computing R(q)) and the definition of the quantile stopping rule

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem R_display (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (q : ℝ) (hq : q ∈ Set.Ioc 0 1) :
    (μ.prod unif01) {p : ℝ × ℝ | stopQ μ q p.1 p.2} = ENNReal.ofReal q ∧
      ∫⁻ p, Set.indicator {p : ℝ × ℝ | stopQ μ q p.1 p.2} (fun p => ENNReal.ofReal p.1) p
          ∂(μ.prod unif01) = Rq μ q ∧
      ENNReal.ofReal q * ENNReal.ofReal (tauQ μ q) +
          ∫⁻ t in Set.Ioi (tauQ μ q), ENNReal.ofReal (1 - cdf μ t) = Rq μ q := by sorry

end CorreaThreshold.Adaptive
