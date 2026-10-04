-- Prove2me | Theorems.Thm_EntropicBarrier_Universal_lemma4_variance_window
-- name    : EntropicBarrier.Universal.lemma4_variance_window
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:04:08.745987+00:00
-- url     : https://prove2.me/theorems/0f427c2f-7265-4253-b06a-ce624105b660
-- title:
--   Lemma 4 — $(1-2c(\varepsilon)\varepsilon\log^2(1/\varepsilon))\mathrm{Var}(X)\le\int_{x_1}^{x_2}(x-x_0)^2\lambda\le\mathbb E(|X-x_0|^2\mid X\in[x_1,x_2])$
-- statement:
--   Let $0<\varepsilon<1$ and let $X$ be a real log-concave random variable with density $\lambda$ ($\lambda$ log-concave, $\int\lambda=1$). Let $x_1<x_0<x_2$ satisfy $\lambda(x_1)<\varepsilon\lambda(x_0)$ and $\lambda(x_2)<\varepsilon\lambda(x_0)$. Then, with
--   $$c(\varepsilon)=\left(1+\frac{2}{\log(1/\varepsilon)}\right)^3\left(1+\frac{2}{\log(1/\varepsilon)}+\frac{2}{\log^2(1/\varepsilon)}\right),$$
--   one has
--   $$\left(1-2c(\varepsilon)\varepsilon\log^2(1/\varepsilon)\right)\mathrm{Var}(X)\le\int_{x_1}^{x_2}(x-x_0)^2\lambda(x)\,dx\le\mathbb E\left(|X-x_0|^2\mid X\in[x_1,x_2]\right).$$
--
--   Lemma 4 converts the conditional second-moment bound (9) into the variance bound (7).
--
--   **Formalization Note** The page says "$\varepsilon>0$"; the statement is false for $\varepsilon\ge1$ (for $\varepsilon=e$, $c=-1$ and the coefficient is $1+2e>1$, and $X$ uniform on $[0,1]$ with $x_1,x_0,x_2=0.4,0.5,0.6$ is a counterexample), the proof uses $\log(1/\varepsilon)>0$ throughout, and the paper applies it only with $\varepsilon<1$; so it is stated for $0<\varepsilon<1$. $\mathrm{Var}(X)=\int x^2\lambda-(\int x\lambda)^2$, and the conditional expectation is the ratio $\int_{[x_1,x_2]}(x-x_0)^2\lambda/\int_{[x_1,x_2]}\lambda$, whose denominator is positive (the hypotheses force $\lambda(x_0)>0$, and a log-concave probability density is positive on an interval of positive length containing $x_0$). Log-concavity is the published `ConvexOptimization.LogConcaveOn Set.univ`; all moments of a log-concave density are finite.
-- source:
--   Bubeck & Eldan, The entropic barrier: a simple and optimal universal self-concordant barrier, arXiv:1412.1587v3 (COLT 2015), p. 8, Lemma 4 (restated and proved pp. 12-13)

import Mathlib
import Definitions.Def_LogConcaveOn
import Definitions.Def_EntropicBarrier_Universal_Marginal

open scoped RealInnerProductSpace
open MeasureTheory

namespace EntropicBarrier.Universal

theorem lemma4_variance_window (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (dens : ℝ → ℝ)
    (hlc : ConvexOptimization.LogConcaveOn Set.univ dens) (hprob : ∫ x, dens x = 1)
    (x₁ x₀ x₂ : ℝ) (h₁₀ : x₁ < x₀) (h₀₂ : x₀ < x₂)
    (hx₁ : dens x₁ < ε * dens x₀) (hx₂ : dens x₂ < ε * dens x₀) :
    (1 - 2 * lemma4Const ε * ε * Real.log (1 / ε) ^ 2) *
        ((∫ x, x ^ 2 * dens x) - (∫ x, x * dens x) ^ 2) ≤
      ∫ x in x₁..x₂, (x - x₀) ^ 2 * dens x ∧
    ∫ x in x₁..x₂, (x - x₀) ^ 2 * dens x ≤
      (∫ x in Set.Icc x₁ x₂, (x - x₀) ^ 2 * dens x) / (∫ x in Set.Icc x₁ x₂, dens x) := by sorry

end EntropicBarrier.Universal
