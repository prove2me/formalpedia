-- Prove2me | Theorems.Thm_CorrelatedTrials_Consistency_lemma_EC_5
-- name    : CorrelatedTrials.Consistency.lemma_EC_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:57.656103+00:00
-- url     : https://prove2.me/theorems/9575f340-0d2a-4816-a183-6430aef608ef
-- title:
--   Lemma EC.5, p. ec7 — $\liminf\nu^*_i(\mu^T,\Sigma^T)=-1$ for all $i$ forces $\Sigma^T_{i,i}\to0$
-- statement:
--   Run the trial under the cPDE allocation policy. Almost surely the following holds: if for every arm $i$
--
--   $$
--   \liminf_{T\to\infty}\nu^*_i(\mu^T,\Sigma^T)=-1,
--   $$
--
--   then $\lim_{T\to\infty}\Sigma^T_{i,i}=0$ for every arm $i$.
--
--   Combined with Lemma EC.4 and the fact that cPDE always samples an arm with the largest index, this yields part i) of Theorem 1.
--
--   **Formalization Note** The index is read as $\nu^*_i(\mu^T,\Sigma^T)$. "$\liminf=-1$" is written as: for every $\varepsilon>0$, $\nu^*_i(\mu^T,\Sigma^T)<-1+\varepsilon$ for infinitely many $T$ (that is, $\liminf\le-1$); since $\nu^*_i\ge-1$, this is the printed hypothesis. Stated for the cPDE process.
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. ec7, Lemma EC.5

import Mathlib
import Definitions.Def_CorrelatedTrials_Consistency_CpdeProcess

open MeasureTheory Filter Topology

namespace CorrelatedTrials.Consistency

/-- Lemma EC.5 (Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), p. ec7, Lemma EC.5):
"If liminf_{T→∞} ν*_i(µ^t, Σ^t) = −1 for all i, then lim_{T→∞} Σ^T_{i,i} = 0 for all i as well."

Along almost every sample path of the cPDE trial, if for every arm `i` the cPDE index
`ν*_i(µ^T, Σ^T)` has `liminf` equal to `−1`, then every posterior variance `Σ^T_{i,i}` tends
to `0`.

Formalization Note:
1. The index is read as `ν*_i(µ^T, Σ^T)`, with the limit variable `T`.
2. "liminf = −1" is encoded as "for every `ε > 0`, `ν*_i(µ^T, Σ^T) < −1 + ε` for infinitely many
   `T`", i.e. `liminf ≤ −1`; since `ν*_i ≥ −1` this is the printed hypothesis.
3. Stated for the cPDE process, the one Theorem 1 uses. -/
theorem lemma_EC_5 {M : ℕ} (I : Instance M) :
    ∀ᵐ ω ∂(trialMeasure I),
      (∀ i, ∀ ε > 0, ∃ᶠ T in atTop, nuStar I.lam I.c (mu I T ω) (Sig I T ω) i < -1 + ε) →
        ∀ i, Tendsto (fun T => Sig I T ω i i) atTop (𝓝 0) := by sorry

end CorrelatedTrials.Consistency
