-- Prove2me | Theorems.Thm_ChoiceRM_Policy_proposition_3
-- name    : ChoiceRM.Policy.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:16.216669+00:00
-- url     : https://prove2.me/theorems/7d1b43d9-3268-48c9-990f-a88a9c47bed0
-- title:
--   Proposition 3, p. 11 — purchase and revenue order agree
-- statement:
--   List nondominated offer sets as $S_1,\ldots,S_m$ in nondecreasing purchase-probability order. Then their expected revenues have the same order:
--
--   $$Q(S_1)\le\cdots\le Q(S_m)\quad\Longrightarrow\quad R(S_1)\le\cdots\le R(S_m).$$
--
--   This permits a single index to order both coordinates of the nondominated frontier.
--
--   **Formalization Note** Only nondominance and the order of purchase probabilities are needed; no dynamic-programming assumptions are used.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 11, Proposition 3

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance

namespace ChoiceRM.Policy

open RevenueManagement

/-- Proposition 3 (p. 11): purchase-probability order also orders expected revenue
among nondominated sets. -/
theorem proposition_3 {n m : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ)
    (Sq : Fin m → Finset (Fin n)) (hnd : ∀ k, IsNondominated P r (Sq k))
    (hmono : Monotone (fun k => purchaseProb P (Sq k))) :
    Monotone (fun k => expRevenue P r (Sq k)) := by sorry

end ChoiceRM.Policy
