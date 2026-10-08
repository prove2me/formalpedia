-- Prove2me | Theorems.Thm_ChoiceRM_Policy_proposition_1
-- name    : ChoiceRM.Policy.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:02.59399+00:00
-- url     : https://prove2.me/theorems/c6f7c167-abd2-4c92-b9a1-441f4eff3dcb
-- title:
--   Proposition 1, p. 8 — supporting price for a nondominated offer set
-- statement:
--   Fix a finite product set with purchase probabilities $Q(S)$ and expected revenues $R(S)$. An offer set $T$ is nondominated in the two-clause sense of Definition 1 exactly when there is a strictly positive value $v$ for which
--
--   $$R(S)-vQ(S)\le R(T)-vQ(T)\qquad\text{for every }S\subseteq N.$$
--
--   Thus every nondominated point of the finite revenue–purchase frontier has a positive supporting price, and every such maximizer is nondominated.
--
--   **Formalization Note** The result is stated for arbitrary real-valued $Q$ and $R$ induced by $P$ and $r$; the model's probability and nonnegative-revenue assumptions are unnecessary for this finite geometric equivalence.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 8, Proposition 1

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance

namespace ChoiceRM.Policy

open RevenueManagement

/-- Proposition 1 (p. 8): a nondominated set maximizes revenue minus a strictly
positive multiple of purchase probability, and conversely. -/
theorem proposition_1 {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ)
    (T : Finset (Fin n)) :
    IsNondominated P r T ↔
      ∃ v : ℝ, 0 < v ∧ ∀ S : Finset (Fin n),
        expRevenue P r S - v * purchaseProb P S ≤
          expRevenue P r T - v * purchaseProb P T := by sorry

end ChoiceRM.Policy
