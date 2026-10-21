-- Prove2me | Theorems.Thm_CorrelatedTrials_Consistency_lemma_EC_4
-- name    : CorrelatedTrials.Consistency.lemma_EC_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:54.856483+00:00
-- url     : https://prove2.me/theorems/5cf1df63-7093-4243-babc-8db244e2cf5b
-- title:
--   Lemma EC.4, p. ec7 — sampling infinitely often gives $\Sigma^T_{i,i}\to0$, which gives $\nu^*_i\to-1$
-- statement:
--   Run the trial under the cPDE allocation policy. On every sample path and for every arm $i$:
--   1. if the policy allocates to arm $i$ at infinitely many times, then $\lim_{T\to\infty}\Sigma^T_{i,i}=0$;
--   2. if $\lim_{T\to\infty}\Sigma^T_{i,i}=0$, then
--
--   $$
--   \lim_{T\to\infty}\nu^*_i(\mu^T,\Sigma^T)=-1 .
--   $$
--
--   Arms that are sampled infinitely often thus lose all value of further sampling, which is one half of the argument for Theorem 1.
--
--   **Formalization Note** The index in part 2 is read as $\nu^*_i(\mu^T,\Sigma^T)$ (the page writes $(\mu^t,\Sigma^t)$ under $\lim_{T\to\infty}$). Both parts are stated for every sample path, since the posterior covariance depends only on the sample counts. The paper derives the lemma from the second inequality of Lemma EC.1, which is false as printed; the lemma itself is stated as printed.
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. ec7, Lemma EC.4

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess

open Filter Topology

namespace CorrelatedTrials.Consistency

/-- Lemma EC.4 (Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. ec7, Lemma EC.4):
"If arm i is sampled infinitely often, then lim_{T→∞} Σ^T_{i,i} = 0. In turn, if
lim_{T→∞} Σ^T_{i,i} = 0, then lim_{T→∞} ν*_i(µ^t, Σ^t) = −1 as well."

On every sample path of the cPDE trial and for every arm `i`: (a) if the policy allocates to
`i` at infinitely many times, then `Σ^T_{i,i} → 0`; (b) if `Σ^T_{i,i} → 0`, then
`ν*_i(µ^T, Σ^T) → −1`.

Formalization Note:
1. The limit in the second sentence is read as `ν*_i(µ^T, Σ^T)`, with the limit variable `T`.
2. Both parts are stated for every sample path: the posterior covariance depends only on the
   sample counts, so neither part is a probabilistic statement.
3. The paper derives the lemma from the second inequality of Lemma EC.1, which is false as
   printed; the lemma itself is true by a direct bound and is stated as printed. -/
theorem lemma_EC_4 {M : ℕ} (I : Instance M) :
    (∀ ω i, (∃ᶠ t in atTop, alloc I t ω = i) →
        Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0)) ∧
      (∀ ω i, Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) →
        Tendsto (fun T => nuStar I.lam I.c (mu I T ω) (Sig I T ω) i) atTop (𝓝 (-1))) := by sorry

end CorrelatedTrials.Consistency
