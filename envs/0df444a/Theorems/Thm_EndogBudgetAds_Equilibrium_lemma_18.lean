-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_18
-- name    : EndogBudgetAds.Equilibrium.lemma_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:48.226012+00:00
-- url     : https://prove2.me/theorems/397f1c81-e6b3-45f9-b1d1-3c211b7efb3e
-- title:
--   Lemma 18, p. 56 — E[Σ_i (W_i^{(1)} − W_i^{(2)}) 1{i ∈ U^W_{k,1}}] ≥ (1/θmax) Σ_i P(i ∈ U^W_{k,1}) ≥ E[Ψ̄_k]/(ϑ log m)
-- statement:
--   Under the standing assumptions, with $m \ge 3$ bidders, for every bidder $k$,
--   $$\mathbb E\Big[\sum_i \big(W^{(1)}_i - W^{(2)}_i\big)\mathbf 1\{i \in U^W_{k,1}\}\Big] \ge \frac{1}{\theta_{\max}} \sum_i \mathbb P\big(i \in U^W_{k,1}\big) \ge \frac{1}{\vartheta \log m}\,\mathbb E[\bar\Psi_k],$$
--   where $W^{(1)}_i, W^{(2)}_i$ are the highest and second highest shaded valuations on item $i$ and $U^W_{k,1}$ is the set of items on which bidder $k$ has the highest shaded valuation.
--
--   The first quantity is bidder $k$'s expected surplus (scaled by $1+r_k$) under the greedy allocation; the lemma compares it with her expected unbudgeted spend.
--
--   **Formalization Note** $\log$ is the natural logarithm. Probabilities are taken under the product exponential law of the valuations.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 56, Lemma 18

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 18, p. 56: for every bidder `k` and `m ≥ 3`,
`E[Σ_i (W_i^{(1)} − W_i^{(2)}) 1{i ∈ U^W_{k,1}}] ≥ (1/θmax) Σ_i P(i ∈ U^W_{k,1}) ≥ (1/(ϑ log m)) E[Ψ̄_k]`. -/
theorem lemma_18 (M : Market) (hM : M.Standing) (hm : 3 ≤ M.m) (k : Fin M.m) :
    (1 / M.θmax) * ∑ i, (valLaw M).real {V | IsTop (fun l => W M V l i) k} ≤
        ∫ V, (∑ i, if IsTop (fun l => W M V l i) k then
          top1 (fun l => W M V l i) - top2 (fun l => W M V l i) else 0) ∂ valLaw M ∧
      1 / (vt M * Real.log M.m) * ∫ V, PsiBar M k V ∂ valLaw M ≤
        (1 / M.θmax) * ∑ i, (valLaw M).real {V | IsTop (fun l => W M V l i) k} := by sorry

end EndogBudgetAds.Equilibrium
