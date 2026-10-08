-- Prove2me | Theorems.Thm_ChoiceRM_Policy_theorem_1
-- name    : ChoiceRM.Policy.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T15:48:53.14031+00:00
-- url     : https://prove2.me/theorems/4b69dcb4-0547-4b5c-a1da-ac611e6cec15
-- title:
--   Theorem 1, p. 15 — optimal nondominated offers and monotone largest index
-- statement:
--   Consider a finite set of fare products with a proper choice model, nonnegative fares and a constant arrival probability $\lambda\in[0,1]$. List every nondominated offer set exactly once as $S_1,\ldots,S_m$, in nondecreasing purchase-probability order. Let $V_t(x)$ be the optimal value with $t$ periods and $x$ units remaining, and $\Delta V_{t-1}(x)$ its marginal capacity value. At every $t,x\ge1$, a greatest index $k^*$ maximizing $R_k-Q_k\Delta V_{t-1}(x)$ exists. Every maximizing index gives an optimal offer set, and
--
--   $$V_t(x)=\lambda\bigl(R_{k^*}-Q_{k^*}\Delta V_{t-1}(x)\bigr)+V_{t-1}(x).$$
--
--   For fixed $t$, the greatest optimal index is nondecreasing with remaining capacity $x$. For fixed $x$, it is nonincreasing with the number $t$ of periods remaining. This gives the paper's ordered optimal policy, including the specified rule for ties.
--
--   **Formalization Note** `Fin n` indexes products, including the empty offer set among subsets. The ordered family is exhaustive and has no repeats. Time counts backward as periods remaining. The assumptions $0\le\lambda\le1$ state that arrival is a probability; $t,x\ge1$ avoid undefined decisions and marginal values at zero. The fare-order convention $r_1\ge\cdots\ge r_n$ is omitted because no result in Section 2 uses it.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 15, Theorem 1; p. 12, equation (7)

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_Policy_Dominance
import Definitions.Def_ChoiceRM_Policy_Value

namespace ChoiceRM.Policy

open RevenueManagement

/-- Theorem 1 (p. 15): choose a nondominated set attaining the stage maximum;
the greatest optimal index rises with capacity and falls with time remaining. -/
theorem theorem_1 {n m : ℕ} (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (P : Finset (Fin n) → Fin n → ℝ) (hP : IsChoiceModel P)
    (r : Fin n → ℝ) (hr : ∀ j, 0 ≤ r j)
    (Sq : Fin m → Finset (Fin n)) (hSq : IsOrderedNondominated P r Sq) :
    (∀ t x, 1 ≤ t → 1 ≤ x →
      ∃ k : Fin m,
        IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x) k ∧
        (∀ l : Fin m,
          (∀ i : Fin m,
            expRevenue P r (Sq i) - purchaseProb P (Sq i) * deltaV lam P r (t - 1) x ≤
              expRevenue P r (Sq l) - purchaseProb P (Sq l) * deltaV lam P r (t - 1) x) →
          IsOptimalOffer lam P r t x (Sq l)) ∧
        V lam P r t x =
          lam * (expRevenue P r (Sq k) - purchaseProb P (Sq k) *
            deltaV lam P r (t - 1) x) + V lam P r (t - 1) x) ∧
    (∀ t x x' (hx : 1 ≤ x) (hxx' : x ≤ x') (ht : 1 ≤ t)
      (k k' : Fin m),
      IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x) k →
      IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x') k' →
      k ≤ k') ∧
    (∀ x t t' (hx : 1 ≤ x) (ht : 1 ≤ t) (htt' : t ≤ t')
      (k k' : Fin m),
      IsLargestMaximizer P r Sq (deltaV lam P r (t - 1) x) k →
      IsLargestMaximizer P r Sq (deltaV lam P r (t' - 1) x) k' →
      k' ≤ k) := by sorry

end ChoiceRM.Policy
