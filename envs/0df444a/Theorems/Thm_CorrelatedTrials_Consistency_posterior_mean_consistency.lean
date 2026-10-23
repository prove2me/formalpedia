-- Prove2me | Theorems.Thm_CorrelatedTrials_Consistency_posterior_mean_consistency
-- name    : CorrelatedTrials.Consistency.posterior_mean_consistency
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T06:15:51.208313+00:00
-- url     : https://prove2.me/theorems/66b72d21-f856-41d0-b5ab-7dd25e08d7e2
-- title:
--   Theorem 1 (i)⇒(iii), p. ec7 — vanishing posterior variance gives a.s. and $L^2$ consistency of $\mu^T_i$
-- statement:
--   Let $(\mu^0,\Sigma^0,\lambda,c)$ be an instance of the correlated clinical-trial model (Assumption 1: $M\ge 2$ arms, $\Sigma^0$ positive definite, $\lambda_j>0$, $c_j>0$), with unknown mean vector $\theta\sim N(\mu^0,\Sigma^0)$ and observations $\theta_j+\sqrt{\lambda_j}\,\varepsilon_{j,k}$, and run the trial forever under the cPDE allocation policy. Let $\mu^T,\Sigma^T$ be the posterior mean and covariance after $T$ observations (Bayesian update (8)).
--
--   Fix an arm $i$ and suppose that
--   $$\lim_{T\to\infty}\Sigma^T_{i,i}=0\quad\text{almost surely.}$$
--   Then the posterior mean of arm $i$ is consistent:
--
--   1. $\lim_{T\to\infty}\mu^T_i=\theta_i$ almost surely;
--   2. for every $T$, $\mu^T_i-\theta_i$ is square integrable, and
--   $$\lim_{T\to\infty}\big\|\mu^T_i-\theta_i\big\|_{L^2}=0,\qquad\text{i.e. }\ \lim_{T\to\infty}\mathbb E\big[(\mu^T_i-\theta_i)^2\big]=0 .$$
--
--   This is the step "(i) $\Rightarrow$ (iii)" of Theorem 1, which the paper takes from the proof of Theorem 1 of Xie, Frazier and Chick (2016): vanishing posterior uncertainty about $\theta_i$ forces the posterior mean to learn $\theta_i$.
--
--   **Formalization Note.** $L^2$ convergence is stated through the $L^2$ norm (`eLpNorm … 2`) together with membership in $L^2$.
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. ec7, B.4 (proof of Theorem 1 iii), applying the argument of Theorem 1 of Xie, Frazier, Chick, Bayesian Optimization via Simulation with Pairwise Sampling and Correlated Prior Beliefs, Operations Research 64(2):542-559 (2016)

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess

open MeasureTheory Filter Topology

namespace CorrelatedTrials.Consistency

/-- Posterior consistency of the cPDE trial (Chick, Gans, Yapar, Bayesian Sequential Learning for
Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31,
2020), p. ec7, proof of Theorem 1 iii), which applies the argument of Theorem 1 of Xie, Frazier,
Chick, Bayesian Optimization via Simulation with Pairwise Sampling and Correlated Prior Beliefs,
Operations Research 64(2):542–559, 2016):
if the posterior variance `Σ^T_{i,i}` of arm `i` tends to `0` almost surely, then the posterior
mean `µ^T_i` tends to `θ_i` almost surely and in `L²`.

Formalization Note: `L²` convergence is stated as: each `µ^T_i − θ_i` lies in `L²`, and its
`L²` norm (`eLpNorm … 2`) tends to `0`. -/
theorem posterior_mean_consistency {M : ℕ} (I : Instance M) (i : Fin M)
    (h : ∀ᵐ ω ∂(trialMeasure I), Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0)) :
    (∀ᵐ ω ∂(trialMeasure I), Tendsto (fun T => mu I T ω i) atTop (𝓝 (theta ω i))) ∧
      (∀ T, MemLp (fun ω => mu I T ω i - theta ω i) 2 (trialMeasure I)) ∧
      Tendsto (fun T => eLpNorm (fun ω => mu I T ω i - theta ω i) 2 (trialMeasure I))
        atTop (𝓝 0) := by sorry

end CorrelatedTrials.Consistency
