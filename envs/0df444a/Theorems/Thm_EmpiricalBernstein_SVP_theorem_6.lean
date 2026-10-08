-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_theorem_6
-- name    : EmpiricalBernstein.SVP.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:10.545298+00:00
-- url     : https://prove2.me/theorems/c23a13f3-6164-40ed-a2cd-cbeed3f2ffd6
-- title:
--   Theorem 6 — uniform empirical Bernstein bound with $\mathcal M(n)=10\mathcal N_\infty(1/n,\mathcal F,2n)$
-- statement:
--   Let $X$ be a random variable with values in a set $\mathcal X$ and distribution $\mu$, and let $\mathcal F$ be a class of hypotheses $f : \mathcal X \to [0,1]$. Fix $\delta \in (0,1)$ and $n \ge 16$, and set
--
--   $$
--   \mathcal M(n) = 10\, \mathcal N_\infty(1/n, \mathcal F, 2n).
--   $$
--
--   Then with probability at least $1-\delta$ in the random vector $\mathbf X = (X_1,\dots,X_n) \sim \mu^n$, for **every** $f \in \mathcal F$,
--
--   $$
--   P(f,\mu) - P_n(f,\mathbf X) \le \sqrt{\frac{18\, V_n(f,\mathbf X)\ln(\mathcal M(n)/\delta)}{n}} + \frac{15\ln(\mathcal M(n)/\delta)}{n-1}.
--   $$
--
--   Here $P(f,\mu) = \mathbb E f(X)$ is the risk, $P_n(f,\mathbf X) = \frac1n\sum_i f(X_i)$ the empirical risk, $V_n(f,\mathbf X)$ the sample variance of $(f(X_1),\dots,f(X_n))$, and $\mathcal N_\infty$ the growth function.
--
--   The bound extends the empirical Bernstein bound uniformly over infinite classes of polynomial growth; it is the ingredient of the excess-risk bound for sample variance penalization (Theorem 15).
--
--   **Formalization Note** The quantifier over $f$ is inside the event: the statement bounds $\mu^n\{\mathbf x : \exists f \in \mathcal F \text{ violating the bound}\}$ by $\delta$. **Added hypotheses**, making precise the paper's "questions of measurability will be ignored throughout, if necessary this is enforced through finiteness assumptions": $\mathcal F$ is countable and each $f\in\mathcal F$ is measurable; and $\mathcal N_\infty(1/n,\mathcal F,2n) < \infty$ (with an infinite $\mathcal M(n)$ the printed bound is vacuous, while Lean's $\infty$-to-real conversion would give $0$). $\mathcal M(n)$ is the real number `calM F n`.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Theorem 6, pp. 2–3

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_EmpiricalBernstein_SVP_sampleVar
import Definitions.Def_EmpiricalBernstein_SVP_growthFunction

open MeasureTheory VarianceRegularization.Expansion

namespace EmpiricalBernstein.SVP

/-- Theorem 6, the uniform empirical Bernstein bound (arXiv:0907.3740v1, pp. 2–3), for a countable
class `F` of measurable `[0,1]`-valued functions with finite growth function `N∞(1/n, F, 2n)`. -/
theorem theorem_6 {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (F : Set (𝒳 → ℝ)) (hFc : F.Countable) (hFm : ∀ f ∈ F, Measurable f)
    (hF01 : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) (hn : 16 ≤ n)
    (hfin : growthFunction (1 / (n : ℝ)) F (2 * n) < ⊤) :
    Measure.pi (fun _ : Fin n => μ) {x | ∃ f ∈ F,
        (∫ y, f y ∂μ) - empMean (fun i => f (x i))
          > Real.sqrt (18 * sampleVar (fun i => f (x i)) * Real.log (calM F n / δ) / n)
            + 15 * Real.log (calM F n / δ) / ((n : ℝ) - 1)}
      ≤ ENNReal.ofReal δ := by sorry

end EmpiricalBernstein.SVP
