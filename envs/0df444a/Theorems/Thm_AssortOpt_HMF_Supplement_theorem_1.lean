-- Prove2me | Theorems.Thm_AssortOpt_HMF_Supplement_theorem_1
-- name    : AssortOpt.HMF.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T07:18:52.210983+00:00
-- url     : https://prove2.me/theorems/7eb91831-cfd5-47c9-9089-40cc1169c8f3
-- title:
--   Theorem 1 — some assortment attains the greatest IC revenue under any Markov-chain choice model
-- statement:
--   Let $D_C$ be the first-visit list distribution of any almost surely terminating Markov-chain choice model $C$, and fix arbitrary nonnegative item prices $r_j$. There is an assortment $S\subseteq N$ such that
--   $$\mathsf{REV}[S]=\max_{x\ \mathrm{IC}}\mathsf{REV}[x],\qquad \mathsf{OPT}^S=\mathsf{OPT}^x.$$
--   The maximum is attained: the displayed assortment revenue belongs to the set of IC revenues and bounds all of them. This companion theorem specializes the mission's published sufficient-condition goal through Proposition 4. No irreducibility or global absorption from inaccessible states is assumed.
--
--   Differences from the source:
--   - encoding: items N={1,…,n} and a finite list distribution → 0-based Fin n and the published ListDist with strictly positive support of Nodup lists; reason: the same finite distributions, including empty lists and n=0, are represented
--   - encoding: Definition 9: first visits of an almost surely terminating Markov chain → a normalized PMF of finite stopped walks with product masses, pushed forward by firstVisits to inducedDist; reason: normalization expresses almost sure absorption under the initial law, permits unbounded walk lengths and imposes no condition on inaccessible states; terminal self-loop padding is unused
--   - reading: Definition 9: 'Start at each state j with probability λ_j (where Σ_j λ_j = 1)', without saying whether j ranges over N or N ∪ {0} → initial law on N ∪ {0} (Option (Fin n)); initial mass λ_0 at the terminal state is allowed and yields the empty list; reason: the MNL instance of Figure 2 (p. 15; Definition 13's 0-ball, p. 20) is a Markov Chain choice model only with λ_0 > 0; λ_0 = 0 recovers the j ∈ N reading, so both readings are covered
-- source:
--   Ma, When is Assortment Optimization Optimal?, arXiv:2105.10433v5, p. 15, Theorem 1

import Mathlib
import Definitions.Def_AssortOpt_HMF_Supplement_MarkovModel

namespace AssortOpt.HMF.Supplement

theorem theorem_1 {n : ℕ} (C : MarkovModel n) (r : Fin n → ℝ)
    (hr : ∀ j, 0 ≤ r j) :
    ∃ S : Finset (Fin n),
      IsGreatest (revMech (inducedDist C) r '' {x | IsIC (inducedDist C) x})
        (revAssort (inducedDist C) r S) := by sorry

end AssortOpt.HMF.Supplement
