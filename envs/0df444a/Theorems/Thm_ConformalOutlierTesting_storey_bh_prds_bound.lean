-- Prove2me | Theorems.Thm_ConformalOutlierTesting_storey_bh_prds_bound
-- name    : ConformalOutlierTesting.storey_bh_prds_bound
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T07:59:02.233578+00:00
-- url     : https://prove2.me/theorems/bdc1186b-1ec5-4daa-a909-649546aa3bc5
-- title:
--   Theorem 7: an FDR bound for Storey's BH with PRDS p-values (with positivity)
-- statement:
--   Let $p=(p_1,\dots,p_m)$ be a random vector that is PRDS on the set $\mathcal H_0$ of nulls. Suppose each null p-value is super-uniform, $\mathbb P[p_i\le t]\le t$ for $t\in[0,1]$, and satisfies $p_i\ge p_{\min}$ almost surely, for a constant $p_{\min}\in[0,1]$. Let $\alpha,\lambda\in(0,1)$, let $A=\sum_iI(p_i\ge\lambda)$, and let
--
--   $$p_*=\max\Big\{\frac{\alpha(1-\lambda)}m,\,p_{\min}\Big\}.$$
--
--   Assume $\mathbb P[p_i\le p_*]>0$ for every $i\in\mathcal H_0$. Then the Storey–BH procedure with parameter $\lambda$ at level $\alpha$ satisfies
--
--   $$\mathbb E\left[\frac{|\mathcal R\cap\mathcal H_0|}{\max\{1,|\mathcal R|\}}\right]\le\alpha(1-\lambda)\sum_{i\in\mathcal H_0}\mathbb E\Big[\frac1{1+A}\,\Big|\,p_i\le p_*\Big].$$
--
--   This bound is not specific to conformal p-values. It applies to any PRDS p-values with an almost-sure lower bound, such as permutation p-values.
--
--   **Formalization Note** The paper conditions on $\{p_i\le p_*\}$ without requiring this event to have positive probability. If it is null, the conditional expectation is undefined while the FDR can be positive. The positivity hypothesis is therefore added. The p-values are assumed measurable.
-- source:
--   Bates, Candès, Lei, Romano and Sesia, Testing for Outliers with Conformal p-values, arXiv:2104.08279v3 (2022), Appendix A.4, Theorem 7, p. 42; definition of the Storey-BH procedure p. 42

import Mathlib
import Definitions.Def_ConformalOutlierTesting_Basic

open MeasureTheory ProbabilityTheory Filter Topology Set BoundedContinuousFunction

namespace ConformalOutlierTesting

theorem storey_bh_prds_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m : ℕ} (p : Ω → Fin m → ℝ) (hp : Measurable p)
    (H₀ : Finset (Fin m)) (hprds : IsPRDS P p H₀)
    (hsu : ∀ i ∈ H₀, ∀ t ∈ Icc (0 : ℝ) 1, P {ω | p ω i ≤ t} ≤ ENNReal.ofReal t)
    (pmin : ℝ) (hpmin : pmin ∈ Icc (0 : ℝ) 1) (hlb : ∀ i ∈ H₀, ∀ᵐ ω ∂P, pmin ≤ p ω i)
    (α lam : ℝ) (hα : α ∈ Ioo (0 : ℝ) 1) (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hpos : ∀ i ∈ H₀, 0 < P {ω | p ω i ≤ max (α * (1 - lam) / m) pmin}) :
    fdr P (fun ω => storeyRej α lam (p ω)) H₀ ≤
      α * (1 - lam) * ∑ i ∈ H₀, ∫ ω, 1 / (1 + (storeyA lam (p ω) : ℝ))
        ∂(ProbabilityTheory.cond P {ω | p ω i ≤ max (α * (1 - lam) / m) pmin}) := by sorry

end ConformalOutlierTesting
