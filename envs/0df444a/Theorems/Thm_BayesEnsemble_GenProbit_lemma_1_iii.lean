-- Prove2me | Theorems.Thm_BayesEnsemble_GenProbit_lemma_1_iii
-- name    : BayesEnsemble.GenProbit.lemma_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:07.490681+00:00
-- url     : https://prove2.me/theorems/bc388a72-f85d-4205-a2d2-6d5b13900889
-- title:
--   Lemma 1(iii), p. 27 — conditional normal law
-- statement:
--   Let $x\sim N(\mu,\Sigma)$, fix expert $i$, and write $Q=\alpha_i x_i$ and $X=\alpha_0+\sum_{j\ne i}\alpha_jx_j$. If $\alpha_i\ne0$ and $\sigma_{ii}>0$, then the conditional law of $X$ given $Q=t$ is normal, for almost every $t$ under the law of $Q$:
--
--   $$
--   X\mid Q=t\sim N\!\left(\theta_{-i}+b_{-i,i}b_{i,i}^{-1}(t-\theta_i),\ v_i\right),\qquad
--   v_i=b_{-i,-i}-b_{-i,i}b_{i,i}^{-1}b_{i,-i}.
--   $$
--
--   Here $\theta_i=\alpha_i\mu_i$, $\theta_{-i}=\alpha_0+\sum_{j\ne i}\alpha_j\mu_j$, $b_{i,i}=\alpha_i^2\sigma_{ii}$, and the remaining $b$ terms are the covariance entries stated in Lemma 1. This is the Gaussian conditioning step used to determine each expert's report.
--
--   **Formalization Note** Conditional distributions are versions, so the equality is almost everywhere in $t$. The paper's equality $b_{i,-i}=b_{-i,i}$ follows from covariance symmetry. The displayed variance is represented by the equivalent Proposition 4 expression in the definition of $v_i$.
-- source:
--   Lichtendahl, Grushka-Cockayne, Jose & Winkler, Bayesian Ensembles of Binary-Event Forecasts: When Is It Appropriate to Extremize or Anti-Extremize?, arXiv:1705.02391v2, p. 27, Lemma 1(iii)

import Mathlib
import Definitions.Def_BayesEnsemble_GenProbit_Model

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace BayesEnsemble.GenProbit

/-- Lemma 1(iii), p. 27: the conditional Gaussian law of the remaining predictor. -/
theorem lemma_1_iii {k : ℕ} (P : Params k) (hS : P.S.PosSemidef)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (x : Ω → EuclideanSpace ℝ (Fin k)) (hx : Measurable x)
    (hlaw : μ.map x = multivariateGaussian P.mean P.S)
    (i : Fin k) (hα : P.alpha i ≠ 0) (hσ : 0 < P.S i i) :
    let Q : Ω → ℝ := fun ω => P.alpha i * x ω i
    let X : Ω → ℝ := fun ω => P.alpha0 +
      ∑ j ∈ Finset.univ.erase i, P.alpha j * x ω j
    ∀ᵐ t ∂(μ.map Q),
      condDistrib X Q μ t =
        gaussianReal (mi P i t) (vi P i).toNNReal := by sorry

end BayesEnsemble.GenProbit
