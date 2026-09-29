-- Prove2me | Theorems.Thm_CachonPushPull_Pareto_qP_characterization
-- name    : CachonPushPull.Pareto.qP_characterization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-26T19:29:02.145369+00:00
-- url     : https://prove2.me/theorems/b18f5006-0e4a-4a4b-83b6-4f1e4c98eed3
-- title:
--   Lemma 4: the indifference quantity $q^P$ exists, is unique, maximizes $\pi_r - \hat\pi_s$, and exceeds $q^*$
-- statement:
--   Let demand satisfy the standing assumptions and $v < c < p$. There is a quantity $q^P > 0$ such that
--
--   1. (i) $q^P$ is the unique $q > 0$ with $\pi_r(q) = \hat\pi_r(q)$;
--   2. (ii) $q^P$ is the unique $q > 0$ with $\pi_s(q) = \hat\pi_s(q)$;
--   3. (iii) $q^P$ maximizes $\pi_r(q) - \hat\pi_s(q)$ over $q \ge 0$, and is its only maximizer there;
--   4. (v) every maximizer $q^*$ of $\pi_r$ over $[0, \infty)$ satisfies $q^P > q^*$.
--
--   Item (iv) of the paper, $q^P = q' = q''$, is expressed by using the single quantity $q^P$ in (i)–(iii).
--
--   At $q^P$ each firm earns the same with the pull and with the push contract; $q^P$ is the lower end of the Pareto set of Theorem 6.
--
--   **Formalization Note** Uniqueness in (i) and (ii) is over $q > 0$, since all four profits vanish at $q = 0$. The existence of a maximizer $q^*$ is Theorem 3.
-- source:
--   Cachon, The Allocation of Inventory Risk in a Supply Chain: Push, Pull, and Advance-Purchase Discount Contracts, Management Science 50(2), 2004, p. 230, Lemma 4

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Profits

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

/-- Lemma 4, p. 230: the quantity `q^P` exists; it is the unique positive quantity where the
retailer is indifferent between pull and push, the unique positive quantity where the supplier is
indifferent, the unique maximizer of `π_r(q) - π̂_s(q)`, and it exceeds every maximizer `q*` of
`π_r`. -/
theorem qP_characterization (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ∃ qP : ℝ, 0 < qP ∧
      (∀ q : ℝ, 0 < q → (pullRetailerProfit μ p c v q = pushRetailerProfit μ p v q ↔ q = qP)) ∧
      (∀ q : ℝ, 0 < q → (pullSupplierProfit μ c v q = pushSupplierProfit μ p c v q ↔ q = qP)) ∧
      IsMaxOn (fun q : ℝ => pullRetailerProfit μ p c v q - pushSupplierProfit μ p c v q)
        (Set.Ici 0) qP ∧
      (∀ q : ℝ, 0 ≤ q →
        IsMaxOn (fun q : ℝ => pullRetailerProfit μ p c v q - pushSupplierProfit μ p c v q)
          (Set.Ici 0) q → q = qP) ∧
      (∀ qstar : ℝ, 0 ≤ qstar → IsMaxOn (pullRetailerProfit μ p c v) (Set.Ici 0) qstar →
        qstar < qP) := by sorry

end CachonPushPull.Pareto
