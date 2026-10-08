-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_lemma_5
-- name    : CorreaThreshold.Adaptive.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:30.535719+00:00
-- url     : https://prove2.me/theorems/a48ef358-6546-4a0c-9335-b9ddafc8545a
-- title:
--   Lemma 5, p. 1463 — if ρ₁ = ⋯ = ρₙ then E(max{X₁, …, Xₙ}) = nγ₁E(X_r)
-- statement:
--   Throughout, $X_1,\ldots,X_n$ are i.i.d. with common law $\mu$ on $\mathbb R$, where $\mu$ is a probability measure with $\mu((-\infty,0))=0$ (the variables are nonnegative), and $F(x)=\mu((-\infty,x])$ is their distribution function. Let $n\ge2$ and $0=\varepsilon_0<\varepsilon_1<\cdots<\varepsilon_n=1$, $A_i=[\varepsilon_{i-1},\varepsilon_i]$, $\psi(q)=(n-1)(1-q)^{n-2}$, $\gamma_i=\int_{A_i}\psi$, $\rho_1=1/\gamma_1$ and $\rho_{i+1}=(\rho_i/\gamma_{i+1})\int_{\varepsilon_{i-1}}^{\varepsilon_i}\psi(q)(1-q)\,dq$ for $i=1,\ldots,n-1$. Let $X_r$ be the value at which the quantile stopping rule stops (and $0$ if it never stops), where the acceptance probabilities $q_i$ are drawn independently with density $\psi/\gamma_i$ on $A_i$, independently of the $X_i$ and of the tie-breaking coins. If $\varepsilon_1,\ldots,\varepsilon_{n-1}$ are chosen such that $\rho_1=\rho_2=\cdots=\rho_n$, then
--   $$E(\max\{X_1,\ldots,X_n\})=n\gamma_1E(X_r).$$
--
--   The approximation factor of the quantile rule is therefore $n\gamma_1$, which the rest of §4 bounds by $\beta^*$.
--
--   **Formalization Note** Both sides are in $[0,\infty]$; $n\ge2$ as in §4.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1463, Lemma 5

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem lemma_5 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (ε : ℕ → ℝ) (hε0 : ε 0 = 0) (hεn : ε n = 1)
    (hεmono : ∀ i < n, ε i < ε (i + 1))
    (hρ : ∀ i ∈ Finset.Icc 1 n, rho n ε i = rho n ε 1) :
    SamuelCahnProphet.IID.Emax μ n = ENNReal.ofReal (n * gam n ε 1) * quantileValue μ n ε := by sorry

end CorreaThreshold.Adaptive
