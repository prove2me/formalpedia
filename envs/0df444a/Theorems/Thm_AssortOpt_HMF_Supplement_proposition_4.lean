-- Prove2me | Theorems.Thm_AssortOpt_HMF_Supplement_proposition_4
-- name    : AssortOpt.HMF.Supplement.proposition_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T07:17:02.042683+00:00
-- url     : https://prove2.me/theorems/4a475151-c6c8-418e-ab63-b7d36f7e4b42
-- title:
--   Proposition 4 — Markov-chain list distributions have history-monotone futures
-- statement:
--   Let $C$ be any Markov-chain choice model of Definition 9, with almost sure termination under its initial law, and let $D_C$ be its induced first-visit list distribution. Then
--   $$D_C\text{ has history-monotone futures}.$$
--   This supplies the sufficient condition needed to apply the published goal to Markov-chain choice models. It uses the published history-monotone-futures predicate without altering it.
--
--   Differences from the source:
--   - encoding: items N={1,…,n} and a finite list distribution → 0-based Fin n and the published ListDist with strictly positive support of Nodup lists; reason: the same finite distributions, including empty lists and n=0, are represented
--   - encoding: Definition 9: first visits of an almost surely terminating Markov chain → a normalized PMF of finite stopped walks with product masses, pushed forward by firstVisits to inducedDist; reason: normalization expresses almost sure absorption under the initial law, permits unbounded walk lengths and imposes no condition on inaccessible states; terminal self-loop padding is unused
--   - reading: Definition 9: 'Start at each state j with probability λ_j (where Σ_j λ_j = 1)', without saying whether j ranges over N or N ∪ {0} → initial law on N ∪ {0} (Option (Fin n)); initial mass λ_0 at the terminal state is allowed and yields the empty list; reason: the MNL instance of Figure 2 (p. 15; Definition 13's 0-ball, p. 20) is a Markov Chain choice model only with λ_0 > 0; λ_0 = 0 recovers the j ∈ N reading, so both readings are covered
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 21, Proposition 4

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_MarkovModel

namespace AssortOpt.HMF.Supplement

theorem proposition_4 {n : ℕ} (C : MarkovModel n) :
    HasHistoryMonotoneFutures (inducedDist C) := by sorry

end AssortOpt.HMF.Supplement
