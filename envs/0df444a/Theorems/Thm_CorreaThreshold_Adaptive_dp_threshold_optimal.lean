-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_dp_threshold_optimal
-- name    : CorreaThreshold.Adaptive.dp_threshold_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:55.978235+00:00
-- url     : https://prove2.me/theorems/f5a8d1ed-e586-4646-a619-e08c94b09052
-- title:
--   Proof of Theorem 2, p. 1464 — the dynamic-programming thresholds τₙ = 0, τᵢ = V_{i+1} are optimal among deterministic threshold rules
-- statement:
--   Throughout, $X_1,\ldots,X_n$ are i.i.d. with common law $\mu$ on $\mathbb R$, where $\mu$ is a probability measure with $\mu((-\infty,0))=0$ (the variables are nonnegative), and $F(x)=\mu((-\infty,x])$ is their distribution function. Assume $E X<\infty$. Let $V_{n+1}=0$ and $V_i=E[\max(X,V_{i+1})]$ for $i=n,\ldots,1$ (so $V_n=E X$), and let $\tau_n=0$, $\tau_i=V_{i+1}$; let $t=\min\{i:X_i\ge\tau_i\}$, with reward $0$ if there is none. Then
--   1. $E(X_t)=V_1$;
--   2. it is irrelevant whether one stops when $X_i\ge\tau_i$ or when $X_i>\tau_i$: every rule that makes either choice at each step earns $E(X_t)$;
--   3. every rule with deterministic thresholds $\tau'_1,\ldots,\tau'_n$, stopping at each step either when $X_i\ge\tau'_i$ or when $X_i>\tau'_i$, earns at most $E(X_t)$:
--   $$E\big(X_{t'}\big)\le E(X_t).$$
--
--   **Formalization Note** The page prints the recurrence as $V_i=E(X\mid X\ge\tau_i)$. That is a slip: the optimal-stopping value is $V_i=E[\max(X,V_{i+1})]=P(X\ge\tau_i)E[X\mid X\ge\tau_i]+P(X<\tau_i)V_{i+1}$ (for $X$ uniform on $[0,1]$ and $n=2$ the printed form gives $V_1=3/4$, the true value is $5/8$); the correct recurrence is formalized. Finite mean is assumed because the $V_i$ are real numbers on the page. Expected rewards are in $[0,\infty]$. Thresholds are indexed 0-based in Lean.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1464, proof of Theorem 2 (first paragraph)

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem dp_threshold_optimal (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (hμint : Integrable (fun x : ℝ => x) μ) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (stopReward (tauDP μ n) x) ∂(SamuelCahnProphet.IID.iidLaw μ n) = ENNReal.ofReal (dpW μ n) ∧
      (∀ σ : Fin n → Bool,
        ∫⁻ x, ENNReal.ofReal (stopRewardMixed (tauDP μ n) σ x) ∂(SamuelCahnProphet.IID.iidLaw μ n) =
          ∫⁻ x, ENNReal.ofReal (stopReward (tauDP μ n) x) ∂(SamuelCahnProphet.IID.iidLaw μ n)) ∧
      ∀ (τ : Fin n → ℝ) (σ : Fin n → Bool),
        ∫⁻ x, ENNReal.ofReal (stopRewardMixed τ σ x) ∂(SamuelCahnProphet.IID.iidLaw μ n) ≤
          ∫⁻ x, ENNReal.ofReal (stopReward (tauDP μ n) x) ∂(SamuelCahnProphet.IID.iidLaw μ n) := by sorry

end CorreaThreshold.Adaptive
