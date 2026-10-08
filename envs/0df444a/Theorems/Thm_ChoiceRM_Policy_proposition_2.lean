-- Prove2me | Theorems.Thm_ChoiceRM_Policy_proposition_2
-- name    : ChoiceRM.Policy.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:50:38.698975+00:00
-- url     : https://prove2.me/theorems/445adebf-4cd5-4dd7-b892-ee0122eef037
-- title:
--   Proposition 2, p. 11 — dominated sets can be excluded
-- statement:
--   At a decision stage with $t\ge1$ periods and $x\ge1$ units remaining, put $d=\Delta V_{t-1}(x)$. Under a proper choice model, nonnegative fares and an arrival probability $\lambda\in[0,1]$:
--
--   1. If $\lambda>0$ and $d>0$, no dominated set maximizes the Bellman stage objective.
--   2. If $d=0$, at least one nondominated set maximizes that objective.
--
--   $$\lambda(R(S)-Q(S)d)$$
--
--   is the objective in both clauses. The result justifies reducing stage optimization to the nondominated frontier.
--
--   **Formalization Note** Strict positivity of $\lambda$ is needed only in the first clause: with zero arrival probability every set is optimal, including dominated ones.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 11, Proposition 2

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance
import Definitions.Def_ChoiceRM_Policy_Value

namespace ChoiceRM.Policy

open RevenueManagement

/-- Proposition 2 (p. 11), with positive arrival probability required only in its
first clause. -/
theorem proposition_2 {n : ℕ} (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (P : Finset (Fin n) → Fin n → ℝ) (hP : IsChoiceModel P)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j) (t x : ℕ) (ht : 1 ≤ t) (hx : 1 ≤ x) :
    ((0 < lam → 0 < deltaV lam P r (t - 1) x →
      ∀ T, IsDominated P r T → ¬ IsOptimalOffer lam P r t x T) ∧
    (deltaV lam P r (t - 1) x = 0 →
      ∃ T, IsNondominated P r T ∧ IsOptimalOffer lam P r t x T)) := by sorry

end ChoiceRM.Policy
