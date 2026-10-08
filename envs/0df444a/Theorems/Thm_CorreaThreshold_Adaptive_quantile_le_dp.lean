-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_quantile_le_dp
-- name    : CorreaThreshold.Adaptive.quantile_le_dp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:55.657734+00:00
-- url     : https://prove2.me/theorems/3f3f8033-9f28-41c0-94f0-adbba979a88f
-- title:
--   Proof of Theorem 2, p. 1464 — E(X_r) ≤ E(X_t): the randomized quantile rule is dominated by the optimal deterministic thresholds
-- statement:
--   Throughout, $X_1,\ldots,X_n$ are i.i.d. with common law $\mu$ on $\mathbb R$, where $\mu$ is a probability measure with $\mu((-\infty,0))=0$ (the variables are nonnegative), and $F(x)=\mu((-\infty,x])$ is their distribution function. Assume $E X<\infty$ and let $\tau_n=0$, $\tau_i=V_{i+1}$ be the dynamic-programming thresholds, with $t=\min\{i:X_i\ge\tau_i\}$. Then
--   For $n\ge2$ and every partition $0=\varepsilon_0<\cdots<\varepsilon_n=1$, the randomized quantile rule of Algorithm 2 satisfies
--   $$E(X_r)\le E(X_t).$$
--
--   Combined with Lemma 5 this gives $E(\max_iX_i)\le n\gamma_1E(X_r)\le n\gamma_1E(X_t)$.
--
--   **Formalization Note** The $V_i$ follow the corrected recurrence $V_i=E[\max(X,V_{i+1})]$ (see the previous milestone). Expected rewards are in $[0,\infty]$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1464, proof of Theorem 2 (second paragraph)

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem quantile_le_dp (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (hμint : Integrable (fun x : ℝ => x) μ) {n : ℕ} (hn : 2 ≤ n) (ε : ℕ → ℝ) (hε0 : ε 0 = 0) (hεn : ε n = 1)
    (hεmono : ∀ i < n, ε i < ε (i + 1)) :
    quantileValue μ n ε ≤
      ∫⁻ x, ENNReal.ofReal (stopReward (tauDP μ n) x) ∂(SamuelCahnProphet.IID.iidLaw μ n) := by sorry

end CorreaThreshold.Adaptive
