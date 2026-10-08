-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_lemma_4
-- name    : CorreaThreshold.Adaptive.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:18.478196+00:00
-- url     : https://prove2.me/theorems/1f63e5f4-6899-4af7-b80c-1e641724e83a
-- title:
--   Lemma 4, p. 1462 — E(X_r) = Σᵢ ρᵢ ∫_{ε_{i−1}}^{εᵢ} (n − 1)(1 − q)^{n−2} R(q) dq
-- statement:
--   Throughout, $X_1,\ldots,X_n$ are i.i.d. with common law $\mu$ on $\mathbb R$, where $\mu$ is a probability measure with $\mu((-\infty,0))=0$ (the variables are nonnegative), and $F(x)=\mu((-\infty,x])$ is their distribution function. Let $n\ge2$ and $0=\varepsilon_0<\varepsilon_1<\cdots<\varepsilon_n=1$, $A_i=[\varepsilon_{i-1},\varepsilon_i]$, $\psi(q)=(n-1)(1-q)^{n-2}$, $\gamma_i=\int_{A_i}\psi$, $\rho_1=1/\gamma_1$ and $\rho_{i+1}=(\rho_i/\gamma_{i+1})\int_{\varepsilon_{i-1}}^{\varepsilon_i}\psi(q)(1-q)\,dq$ for $i=1,\ldots,n-1$. Let $X_r$ be the value at which the quantile stopping rule stops (and $0$ if it never stops), where the acceptance probabilities $q_i$ are drawn independently with density $\psi/\gamma_i$ on $A_i$, independently of the $X_i$ and of the tie-breaking coins. Then
--   $$E(X_r)=\sum_{i=1}^n\rho_i\int_{\varepsilon_{i-1}}^{\varepsilon_i}(n-1)(1-q)^{n-2}R(q)\,dq.$$
--
--   Together with (7), this lets the partition $\varepsilon$ be tuned so that $E(X_r)$ is a fixed multiple of $E(\max_iX_i)$.
--
--   **Formalization Note** $E(X_r)$ and $R$ are in $[0,\infty]$; $\rho_i>0$ under the hypotheses. $n\ge2$ is the range of §4 (for $n=1$, $\psi\equiv0$ and $\gamma_1=0$). The partition, $\gamma_i$ and $\rho_i$ keep the paper's 1-based index.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1462, Lemma 4

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem lemma_4 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {n : ℕ} (hn : 2 ≤ n) (ε : ℕ → ℝ) (hε0 : ε 0 = 0) (hεn : ε n = 1)
    (hεmono : ∀ i < n, ε i < ε (i + 1)) :
    quantileValue μ n ε =
      ∑ i ∈ Finset.Icc 1 n, ENNReal.ofReal (rho n ε i) *
        ∫⁻ q in Set.Icc (ε (i - 1)) (ε i), ENNReal.ofReal (psi n q) * Rq μ q := by sorry

end CorreaThreshold.Adaptive
