-- Prove2me | Theorems.Thm_ChoiceRM_MNL_mnl_purchaseProb_mono
-- name    : ChoiceRM.MNL.mnl_purchaseProb_mono
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:51:56.809985+00:00
-- url     : https://prove2.me/theorems/e9dab7e2-d36f-4ec5-98be-cbe56f388525
-- title:
--   Proof of Proposition 6, p. 24 — the MNL purchase probability Q(S) is increasing in S
-- statement:
--   Let $w_1, \dots, w_n > 0$ and let $P_j(S) = w_j / (\sum_{i\in S} w_i + 1)$ for $j \in S$ be the MNL choice probabilities (14). Then the total purchase probability
--   $$
--   Q(S) = \sum_{j \in S} P_j(S) = \frac{\sum_{i \in S} w_i}{\sum_{i\in S} w_i + 1}
--   $$
--   is increasing in $S$: $Q(S) \le Q(T)$ whenever $S \subseteq T \subseteq N$.
--
--   This is condition (i) of the nesting-by-fare-order property (Definition 4) for the MNL model.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 24, proof of Proposition 6, first paragraph

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_MNL_FareOrder
import Definitions.Def_ChoiceRM_MNL_Models

namespace ChoiceRM.MNL

open RevenueManagement

/-- Proof of Proposition 6, p. 24: under the MNL model (14) with positive weights, the purchase
probability `Q(S) = Σ_{j∈S} P_j(S)` is increasing in `S`. -/
theorem mnl_purchaseProb_mono {n : ℕ} (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (S T : Finset (Fin n)) (hST : S ⊆ T) :
    purchaseProb (mnl w) S ≤ purchaseProb (mnl w) T := by sorry

end ChoiceRM.MNL
