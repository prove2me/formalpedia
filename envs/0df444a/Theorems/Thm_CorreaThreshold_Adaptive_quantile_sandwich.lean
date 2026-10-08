-- Prove2me | Theorems.Thm_CorreaThreshold_Adaptive_quantile_sandwich
-- name    : CorreaThreshold.Adaptive.quantile_sandwich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:06.128082+00:00
-- url     : https://prove2.me/theorems/a444ba61-6a29-4b7f-aeb1-5876f70007b6
-- title:
--   §4, p. 1461 — P(X ≥ τ(q)) ≥ q ≥ P(X > τ(q)) = 1 − F(τ(q)), with equalities if F is continuous at τ(q)
-- statement:
--   Throughout, $X_1,\ldots,X_n$ are i.i.d. with common law $\mu$ on $\mathbb R$, where $\mu$ is a probability measure with $\mu((-\infty,0))=0$ (the variables are nonnegative), and $F(x)=\mu((-\infty,x])$ is their distribution function. Let $F^{-1}(p)=\inf\{x\ge0:F(x)\ge p\}$ and $\tau(q)=F^{-1}(1-q)$. For every $q\in(0,1]$,
--   $$P(X\ge\tau(q))\ \ge\ q\ \ge\ P(X>\tau(q))=1-F(\tau(q)),$$
--   and if $F$ is continuous at $\tau(q)$ both inequalities are equalities.
--
--   This is what makes the quantile stopping rule well defined: the tie-breaking probability $s$ lies in $[0,1]$, and the rule accepts with probability exactly $q$.
--
--   **Formalization Note** $q=0$ is excluded because Lean's $\tau(0)=F^{-1}(1)$ is the junk value $0$ when the support of $F$ is unbounded. Probabilities are measures in $[0,\infty]$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1461, §4 (sentence after the definition of τ(q))

import Mathlib
import Definitions.Def_CorreaThreshold_Adaptive_Setting

namespace CorreaThreshold.Adaptive

open MeasureTheory ProbabilityTheory

theorem quantile_sandwich (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ (Set.Iio 0) = 0)
    (q : ℝ) (hq : q ∈ Set.Ioc 0 1) :
    ENNReal.ofReal q ≤ μ (Set.Ici (tauQ μ q)) ∧
      μ (Set.Ioi (tauQ μ q)) ≤ ENNReal.ofReal q ∧
      μ (Set.Ioi (tauQ μ q)) = ENNReal.ofReal (1 - cdf μ (tauQ μ q)) ∧
      (ContinuousAt (cdf μ) (tauQ μ q) →
        μ (Set.Ici (tauQ μ q)) = ENNReal.ofReal q ∧ μ (Set.Ioi (tauQ μ q)) = ENNReal.ofReal q) := by sorry

end CorreaThreshold.Adaptive
