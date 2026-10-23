-- Prove2me | Theorems.Thm_CorrelatedTrials_Consistency_lemma_EC_3
-- name    : CorrelatedTrials.Consistency.lemma_EC_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:58.141977+00:00
-- url     : https://prove2.me/theorems/3592755d-6906-4503-bfbb-9115c0da2664
-- title:
--   Lemma EC.3, p. ec6 — $\liminf\nu^{cKG_1}_i(\mu^T,\Sigma^T)=-1$ for all $i$ forces $\Sigma^T_{i,i}\to0$
-- statement:
--   Run the trial under the cPDE allocation policy, with posterior means $\mu^T$ and covariances $\Sigma^T$. Almost surely the following holds: if for every arm $i$
--
--   $$
--   \liminf_{T\to\infty}\nu^{cKG_1}_i(\mu^T,\Sigma^T)=-1,
--   $$
--
--   then $\lim_{T\to\infty}\Sigma^T_{i,i}=0$ for every arm $i$.
--
--   This is the lemma of Xie, Frazier and Chick (2016) for one-step knowledge-gradient indices, adapted to sampling one arm at a time; with Lemma EC.1 it yields Lemma EC.5.
--
--   **Formalization Note** "$\liminf=-1$" is written as: for every $\varepsilon>0$, $\nu^{cKG_1}_i(\mu^T,\Sigma^T)<-1+\varepsilon$ for infinitely many $T$ (that is, $\liminf\le-1$). Since $\nu^{cKG_1}_i\ge-1$ always, this is the printed hypothesis. The paper's lemma holds for any allocation policy; it is stated for the cPDE process, the one Theorem 1 concerns.
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. ec6, Lemma EC.3

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess

open MeasureTheory Filter Topology

namespace CorrelatedTrials.Consistency

/-- Lemma EC.3 (Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. ec6, Lemma EC.3):
"If liminf_{T→∞} ν^{cKG1}_i(µ^T, Σ^T) = −1 for all i, then lim_{T→∞} Σ^T_{i,i} = 0 for all i as
well."

Along almost every sample path of the cPDE trial, if for every arm `i` the one-step cKG index
`ν^{cKG1}_i(µ^T, Σ^T)` has `liminf` equal to `−1`, then every posterior variance
`Σ^T_{i,i}` tends to `0`.

Formalization Note:
1. "liminf = −1" is encoded as "for every `ε > 0`, `ν^{cKG1}_i(µ^T, Σ^T) < −1 + ε` for infinitely
   many `T`", i.e. `liminf ≤ −1`. Since `ν^{cKG1}_i ≥ −1` always (Jensen), this is the printed
   hypothesis; as a hypothesis it is no stronger.
2. The paper's lemma holds for any allocation policy; it is stated here for the cPDE process,
   the one Theorem 1 uses. -/
theorem lemma_EC_3 {M : ℕ} (I : Instance M) :
    ∀ᵐ ω ∂(trialMeasure I),
      (∀ i, ∀ ε > 0, ∃ᶠ T in atTop, nuCKG1 I.lam I.c (mu I T ω) (Sig I T ω) i < -1 + ε) →
        ∀ i, Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) := by sorry

end CorrelatedTrials.Consistency
