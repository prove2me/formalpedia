-- Prove2me | Theorems.Thm_EmpiricalBernstein_SVP_svp_excess_risk
-- name    : EmpiricalBernstein.SVP.svp_excess_risk
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:14.194986+00:00
-- url     : https://prove2.me/theorems/0fdc815d-488f-44c2-8b93-d03182c372a5
-- title:
--   Theorem 15 — sample variance penalization has excess risk $\le\sqrt{32V(f^*,\mu)\ln(3\mathcal M(n)/\delta)/n}+22\ln(3\mathcal M(n)/\delta)/(n-1)$
-- statement:
--   Let $X$ be a random variable with values in a set $\mathcal X$ and distribution $\mu$, and let $\mathcal F$ be a class of hypotheses $f : \mathcal X \to [0,1]$. Fix $\delta \in (0,1)$ and $n \ge 2$, and set
--
--   $$
--   \mathcal M(n) = 10\,\mathcal N_\infty(1/n,\mathcal F,2n), \qquad \lambda = \sqrt{18\ln(3\mathcal M(n)/\delta)} .
--   $$
--
--   **Sample variance penalization** selects, from a sample $\mathbf X$, a hypothesis
--
--   $$
--   SVP_\lambda(\mathbf X) \in \arg\min_{f\in\mathcal F}\; P_n(f,\mathbf X) + \lambda\sqrt{\frac{V_n(f,\mathbf X)}{n}} .
--   $$
--
--   Fix $f^* \in \mathcal F$. Then with probability at least $1-\delta$ in the draw of $\mathbf X \sim \mu^n$,
--
--   $$
--   P(SVP_\lambda(\mathbf X),\mu) - P(f^*,\mu) \le \sqrt{\frac{32\, V(f^*,\mu)\ln(3\mathcal M(n)/\delta)}{n}} + \frac{22\ln(3\mathcal M(n)/\delta)}{n-1}.
--   $$
--
--   Here $P(f,\mu)=\mathbb Ef(X)$, $V(f,\mu) = \mathbb Vf(X)$, $P_n$ and $V_n$ are the sample mean and sample variance of $(f(X_1),\dots,f(X_n))$, and $\mathcal N_\infty$ is the growth function.
--
--   Taking $f^*$ optimal, the excess risk of the selected hypothesis is controlled by the variance of an optimal hypothesis: it decays as $(\ln\mathcal M(n))/n$ when some optimal hypothesis has zero variance, whereas empirical risk minimization can be stuck at order $1/\sqrt n$.
--
--   **Formalization Note** The selector is any function `svp` that returns, for every sample, an element of $\mathcal F$ minimizing the penalized objective with the stated $\lambda$; every minimizer is covered, as the paper's $\arg\min$ presupposes one exists. No measurability of `svp` is assumed: the probability of the bad event is its outer measure under $\mu^n$. **Added hypotheses**, making the paper's convention on measurability precise: $\mathcal F$ countable with measurable members, and $\mathcal N_\infty(1/n,\mathcal F,2n)<\infty$ ($\mathcal M(n)$ is the real number `calM F n`). $V(f^*,\mu)$ is Mathlib's `variance`. $n\ge2$ is as printed.
-- source:
--   Maurer, Pontil, Empirical Bernstein Bounds and Sample Variance Penalization, arXiv:0907.3740v1, Theorem 15, p. 6

import Mathlib
import Definitions.Def_VarianceRegularization_Expansion_empMean
import Definitions.Def_EmpiricalBernstein_SVP_sampleVar
import Definitions.Def_EmpiricalBernstein_SVP_growthFunction

open MeasureTheory ProbabilityTheory VarianceRegularization.Expansion

namespace EmpiricalBernstein.SVP

/-- Theorem 15 (arXiv:0907.3740v1, p. 6): excess risk of sample variance penalization (10) with
`λ = √(18 ln(3ℳ(n)/δ))`. `svp` is any selector returning, for every sample `x`, a minimizer over
`F` of `P_n(f, x) + λ √(V_n(f, x)/n)` (the paper's `arg min`). `F` is a countable class of
measurable `[0,1]`-valued functions with finite growth function `N∞(1/n, F, 2n)`. The probability
of the (possibly non-measurable) bad event is its outer measure under `μ^n`. -/
theorem svp_excess_risk {𝒳 : Type*} [MeasurableSpace 𝒳] (μ : Measure 𝒳) [IsProbabilityMeasure μ]
    (F : Set (𝒳 → ℝ)) (hFc : F.Countable) (hFm : ∀ f ∈ F, Measurable f)
    (hF01 : ∀ f ∈ F, ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (n : ℕ) (hn : 2 ≤ n)
    (hfin : growthFunction (1 / (n : ℝ)) F (2 * n) < ⊤)
    (lam : ℝ) (hlam : lam = Real.sqrt (18 * Real.log (3 * calM F n / δ)))
    (fstar : 𝒳 → ℝ) (hfstar : fstar ∈ F)
    (svp : (Fin n → 𝒳) → (𝒳 → ℝ)) (hsvpF : ∀ x, svp x ∈ F)
    (hsvp : ∀ x, ∀ f ∈ F,
      empMean (fun i => svp x (x i)) + lam * Real.sqrt (sampleVar (fun i => svp x (x i)) / n)
        ≤ empMean (fun i => f (x i)) + lam * Real.sqrt (sampleVar (fun i => f (x i)) / n)) :
    Measure.pi (fun _ : Fin n => μ) {x |
        (∫ y, svp x y ∂μ) - (∫ y, fstar y ∂μ)
          > Real.sqrt (32 * variance fstar μ * Real.log (3 * calM F n / δ) / n)
            + 22 * Real.log (3 * calM F n / δ) / ((n : ℝ) - 1)}
      ≤ ENNReal.ofReal δ := by sorry

end EmpiricalBernstein.SVP
