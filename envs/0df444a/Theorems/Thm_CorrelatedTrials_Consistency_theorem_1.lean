-- Prove2me | Theorems.Thm_CorrelatedTrials_Consistency_theorem_1
-- name    : CorrelatedTrials.Consistency.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:56.193101+00:00
-- url     : https://prove2.me/theorems/c5b13ec7-0921-446e-add0-14b38bd62045
-- title:
--   Theorem 1, p. 13 — the cPDE allocation policy is asymptotically consistent
-- statement:
--   Let $(\mu^0,\Sigma^0,\lambda,c)$ be an instance: $M\ge2$ arms, a positive definite prior covariance $\Sigma^0$, sampling variances $\lambda_i>0$ and costs $c_i>0$ (Assumption 1). Run the trial forever under the cPDE allocation policy, which at each time samples an arm maximizing the index $\nu^*_i(\mu^t,\Sigma^t)$ of (EC.8). Then:
--   1. for each arm $i$, $\lim_{T\to\infty}\Sigma^T_{i,i}=0$ almost surely;
--   2. for each arm $i$, $\lim_{T\to\infty}\nu^*_i(\mu^T,\Sigma^T)=-1$ almost surely;
--   3. for each arm $i$, $\lim_{T\to\infty}\mu^T_i=\theta_i$ almost surely, and in $L^2$: each $\mu^T_i-\theta_i$ is square integrable and
--   $$
--   \lim_{T\to\infty}\mathbb E\big[(\mu^T_i-\theta_i)^2\big]=0;
--   $$
--   4. almost surely, $\theta$ has a unique maximizing arm $i^*$, and for all sufficiently large $T$ the posterior mean $\mu^T$ has the same unique maximizing arm $i^*$.
--
--   So cPDE learns every arm's mean and eventually identifies the best intervention; the value per unit cost of further sampling tends to zero (the index tends to $-1$, the normalized cost of one sample).
--
--   **Formalization Note**
--   1. $\nu^*_i$ is (EC.8), with the term $-\frac1{c_i}\max_j\mu_j$ that (15) omits; its supremum is over bounded stopping times, which has the same value.
--   2. Assumption 1 iii) holds trivially because every arm is eligible at every time.
--   3. Ties in the cPDE argmax go to the least index (the paper: at random).
--   4. The $k$-th sample of arm $i$ is $\theta_i+\sqrt{\lambda_i}\,\varepsilon_{i,k}$ with i.i.d. standard normal $\varepsilon_{i,k}$ independent of $\theta$.
--   5. Part ii) is read with $(\mu^T,\Sigma^T)$; part iv), whose printed "for each $i$" plays no role, is read as uniqueness of the maximizer of $\theta$ plus eventual agreement of the unique maximizer of $\mu^T$.
--   6. The $L^2$ convergence is stated through the $L^2$ norm (`eLpNorm`) with membership in $L^2$, not through an integral that would be $0$ for a non-integrable function.
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. 13, Theorem 1 (proof pp. ec3–ec7, B.4)

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess

open MeasureTheory Filter Topology

namespace CorrelatedTrials.Consistency

/-- Theorem 1 (Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. 13, Theorem 1; proof pp. ec3–ec7):
"Suppose Assumption 1 holds. Then i) lim_{T→∞} Σ^T_{i,i} = 0 almost surely for each i;
ii) lim_{T→∞} ν*_i(µ^t, Σ^t) = −1 almost surely for each i; iii) lim_{T→∞} µ^T_i = θ_i almost
surely and in L² for each i; and iv) lim_{T→∞} arg max{µ^T_i} = arg max{θ_i} almost surely for
each i."

Run the trial forever under the cPDE allocation policy. Then for each arm `i`, almost surely:
i) `Σ^T_{i,i} → 0`; ii) `ν*_i(µ^T, Σ^T) → −1`; iii) `µ^T_i → θ_i`, and also in `L²` (each
`µ^T_i − θ_i` is in `L²` and its `L²` norm tends to `0`); iv) almost surely `θ` has a unique
maximizing arm `i*`, and `µ^T` has the same unique maximizing arm for all large `T`.

Formalization Note:
1. `ν*_i` is (EC.8), not (15) (which lacks `−(1/c_i) max_j µ_j`).
2. The supremum in (EC.8) is over bounded stopping times `1 ≤ T_i ≤ N` (same value).
3. Assumption 1 is the structure `Instance` (`M ≥ 2`, `Σ0` positive definite, `λ_i > 0`,
   `c_i > 0`, `∆ = 1`); Assumption 1 iii) is trivial because every arm is eligible
   (`M_t = M`).
4. Ties in the cPDE argmax are broken toward the least index (the paper: randomly).
5. The `k`-th sample of arm `i` is `θ_i + √λ_i ε_{i,k}` with i.i.d. standard normal
   `ε_{i,k}` independent of `θ`.
6. ii) is read with `(µ^T, Σ^T)`; iv) as "θ has a unique maximizer and `µ^T` eventually has the
   same unique maximizer".
7. Arms are `Fin M`, 0-based; time `t` counts the observations so far. -/
theorem theorem_1 {M : ℕ} (I : Instance M) :
    (∀ i, ∀ᵐ ω ∂(trialMeasure I), Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0)) ∧
      (∀ i, ∀ᵐ ω ∂(trialMeasure I),
        Tendsto (fun T => nuStar I.lam I.c (mu I T ω) (Sig I T ω) i) atTop (𝓝 (-1))) ∧
      (∀ i, (∀ᵐ ω ∂(trialMeasure I), Tendsto (fun T => mu I T ω i) atTop (𝓝 (theta ω i))) ∧
        (∀ T, MemLp (fun ω => mu I T ω i - theta ω i) 2 (trialMeasure I)) ∧
        Tendsto (fun T => eLpNorm (fun ω => mu I T ω i - theta ω i) 2 (trialMeasure I))
          atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂(trialMeasure I), ∃ i, (∀ j, j ≠ i → theta ω j < theta ω i) ∧
        ∀ᶠ T in atTop, ∀ j, j ≠ i → mu I T ω j < mu I T ω i) := by sorry

end CorrelatedTrials.Consistency
