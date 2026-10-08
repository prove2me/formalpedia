-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_theorem_2
-- name    : CorreaThreshold.Adaptive.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:48.694985+00:00
-- url     : https://prove2.me/theorems/9c4c47c7-6b5c-4e6c-8c6c-6fdd47bce4aa
-- title:
--   Theorem 2, p. 1464 — for nonnegative i.i.d. X₁, …, Xₙ some thresholds τᵢ give E(max{X₁, …, Xₙ}) ≤ β*E(X_t), β* the solution of (2)
-- statement:
--   Throughout, $X_1,\ldots,X_n$ are i.i.d. with common law $\mu$ on $\mathbb R$, where $\mu$ is a probability measure with $\mu((-\infty,0))=0$ (the variables are nonnegative), and $F(x)=\mu((-\infty,x])$ is their distribution function. Let $n\ge1$ and let $\beta^*>1$ be the unique solution of
--   $$\int_0^1\frac{dy}{y(1-\ln y)+(\beta-1)}=1,\qquad(2)$$
--   $\beta^*\approx1.341$. Then there exist thresholds $\tau_1,\ldots,\tau_n\in\mathbb R$ such that
--   $$E(\max\{X_1,\ldots,X_n\})\le\beta^*\,E(X_t),\qquad t:=\min\{i\in\{1,\ldots,n\}:X_i\ge\tau_i\}.$$
--
--   The thresholds depend on the step $i$ (an adaptive rule), and the guarantee $1/\beta^*\approx0.745$ is the best possible for i.i.d. prophet inequalities.
--
--   **Formalization Note** $\beta^*$ is carried by its defining equation (2) together with $\beta^*>1$ (for $\beta\le1$ the integral of (2) diverges, and the uniqueness of the solution is a separate milestone). $X_t$ is taken to be $0$ when no $X_i$ reaches its threshold; the page leaves this case undefined, and $0$ is the least favourable choice. Expectations are lower Lebesgue integrals in $[0,\infty]$, so infinite means are covered. The page's "$\beta^*\approx1.341>1/0.745$" has its inequality reversed ($\beta^*=1.3415\ldots<1/0.745=1.3423\ldots$) and is not formalized; the intended $1/\beta^*>0.745$ is a separate companion statement. Indices are 0-based in Lean.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1464, Theorem 2 (first stated p. 1456)

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem theorem_2 (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    {n : ℕ} [NeZero n] (β : ℝ) (hβ1 : 1 < β)
    (hβ : ∫ y in (0 : ℝ)..1, 1 / (y * (1 - Real.log y) + (β - 1)) = 1) :
    ∃ τ : Fin n → ℝ, SamuelCahnProphet.IID.Emax μ n ≤
      ENNReal.ofReal β *
        ∫⁻ x, ENNReal.ofReal (stopReward τ x) ∂(SamuelCahnProphet.IID.iidLaw μ n) := by sorry

end CorreaThreshold.Adaptive
