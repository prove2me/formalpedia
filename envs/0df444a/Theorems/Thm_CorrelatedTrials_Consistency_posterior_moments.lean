-- Prove2me | Theorems.Thm_CorrelatedTrials_Consistency_posterior_moments
-- name    : CorrelatedTrials.Consistency.posterior_moments
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T06:24:42.947748+00:00
-- url     : https://prove2.me/theorems/7355141d-bab9-464b-936a-1ba78e5d73a5
-- title:
--   (8), p. 9 — under cPDE, $\mathbb E[\theta_i\mid\mathcal F_T]=\mu^T_i$ and $\mathbb E[(\theta_i-\mu^T_i)^2\mid\mathcal F_T]=\Sigma^T_{i,i}$
-- statement:
--   Let $(\mu^0,\Sigma^0,\lambda,c)$ be an instance of the correlated clinical-trial model (Assumption 1), with unknown mean vector $\theta\sim N(\mu^0,\Sigma^0)$ and i.i.d. standard normal noises $\varepsilon_{j,k}$ independent of $\theta$; the $k$-th sample of arm $j$ is $\theta_j+\sqrt{\lambda_j}\,\varepsilon_{j,k}$. Run the trial under the cPDE allocation policy: at time $s$ arm $u_s$ is sampled, producing the observation $Y_s$ (the next unused sample of arm $u_s$), and the belief $(\mu^s,\Sigma^s)$ is updated by the Bayesian formula (8).
--
--   Fix a time $T$ and an arm $i$, and let
--   $$\mathcal F_T=\sigma(Y_0,\dots,Y_{T-1})$$
--   be the information carried by the first $T$ observations. Then:
--
--   1. the observation vector $(Y_0,\dots,Y_{T-1})$ is measurable;
--   2. $\mu^T_i$ and $\Sigma^T_{i,i}$ are $\mathcal F_T$-measurable;
--   3. almost surely,
--   $$\mathbb E[\theta_i\mid\mathcal F_T]=\mu^T_i,\qquad \mathbb E\big[(\theta_i-\mu^T_i)^2\mid\mathcal F_T\big]=\Sigma^T_{i,i}.$$
--
--   This is the content of the paper's statement that, given the observations so far, the posterior distribution of $\theta$ is $N(\mu^T,\Sigma^T)$, with $(\mu^T,\Sigma^T)$ computed recursively by (8), here for the adaptively allocated observations of the cPDE policy; only the first two conditional moments are asserted. It is the probabilistic input behind the consistency statements of Theorem 1 (posterior means form a martingale, and the posterior variance measures the mean-square error).
--
--   **Formalization Note.** The observation $Y_s$ is the sample of arm $u_s$ with index $n^s_{u_s}$ (the number of earlier samples of that arm); $\mathcal F_T$ is the comap σ-algebra of the map $\omega\mapsto(Y_s(\omega))_{s<T}$.
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. 9, eq. (8) (posterior N(mu^{t+tau}, Sigma^{t+tau}) of theta given the observations), used in B.4, p. ec7

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess

open MeasureTheory

namespace CorrelatedTrials.Consistency

/-- The Bayesian update (8) under the cPDE policy computes the first two posterior moments
(Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated
Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. 9, (8): "the posterior
distribution of θ given the first t + τ observations is N(µ^{t+τ}, Σ^{t+τ})").

Let `F_T = σ(Y_0, …, Y_{T−1})` be the σ-algebra of the first `T` observations
`Y_s = W_{u_s, n^s_{u_s}}` (the `n^s_{u_s}`-th sample of the arm `u_s` allocated at time `s`).
Then the observation history is measurable, `µ^T_i` and `Σ^T_{i,i}` are `F_T`-measurable, and
almost surely `E[θ_i | F_T] = µ^T_i` and `E[(θ_i − µ^T_i)² | F_T] = Σ^T_{i,i}`.

Formalization Note: only the first two conditional moments of the Gaussian posterior
`N(µ^T, Σ^T)` are stated, for the cPDE allocation process. -/
theorem posterior_moments {M : ℕ} (I : Instance M) (T : ℕ) (i : Fin M) :
    Measurable (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) ∧
      StronglyMeasurable[MeasurableSpace.comap
          (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) inferInstance]
        (fun ω => mu I T ω i) ∧
      StronglyMeasurable[MeasurableSpace.comap
          (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) inferInstance]
        (fun ω => Sig I T ω i i) ∧
      (fun ω => mu I T ω i) =ᵐ[trialMeasure I]
        (trialMeasure I)[fun ω => theta ω i | MeasurableSpace.comap
          (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) inferInstance] ∧
      (fun ω => Sig I T ω i i) =ᵐ[trialMeasure I]
        (trialMeasure I)[fun ω => (theta ω i - mu I T ω i) ^ 2 | MeasurableSpace.comap
          (fun ω (s : Fin T) => W I (alloc I s ω) (count I s ω (alloc I s ω)) ω) inferInstance] := by
  sorry

end CorrelatedTrials.Consistency
