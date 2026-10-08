-- Prove2me | Theorems.Thm_CachonCoord_DemandUpdate_p65_supplier_fills
-- name    : CachonCoord.DemandUpdate.p65_supplier_fills
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:58:22.707556+00:00
-- url     : https://prove2.me/theorems/be871b83-f6fd-4d86-b2c7-023c44524ce6
-- title:
--   §6.6.1, p. 65 — Π₂(y|x, q₁, q₂, ξ) = (1 − λ)(Ω₂(y|q₁, ξ) − c₂q₁) + c₂x − w₂q₁; the supplier fills q₂ ≤ q₂(q₁, ξ)
-- statement:
--   Take buy back terms with $\lambda \in [0,1]$, $p - b = \lambda p$ and $w_2 = \lambda c_2 + b$.
--
--   1. For all arguments the supplier's period-2 profit satisfies
--   $$\Pi_2(y\,|\,x,q_1,q_2,\xi) = (1-\lambda)\big(\Omega_2(y\,|\,q_1,\xi) - c_2 q_1\big) + c_2 x - w_2 q_1 .$$
--   2. Let $q_1 \le x < q_2$, where $x$ is the supply chain's inventory at the start of period 2. Suppose $q_2 \le q_2(q_1,\xi)$ for a supply chain optimal period-2 order $q_2(q_1,\xi)$, i.e. a maximizer of $\Omega_2(\cdot\,|\,q_1,\xi)$ over $q_2 \ge q_1$. Then delivering in full, $y = q_2$, maximizes $\Pi_2(y\,|\,x,q_1,q_2,\xi)$ over $x \le y \le q_2$.
--
--   3. Conversely, if $\lambda < 1$, $q_1 \le x < q_2$ and $q_2 > q_2(q_1,\xi)$ (the retailer orders too much), then $y = q_2$ does not maximize $\Pi_2(y\,|\,x,q_1,q_2,\xi)$ over $x \le y \le q_2$: the supplier does not fill the order.
--
--   Thus, even under voluntary compliance, the supplier fills any retailer order that does not exceed the supply chain optimum.
--
--   **Formalization Note** "Fills entirely" is read as: $y = q_2$ is a maximizer over $[x, q_2]$. At $\lambda = 1$ the supplier's profit does not depend on $y$, and filling is one of her optima.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, p. 65, the display of Π₂(y|x, q₁, q₂, ξ) and the sentence after it

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 65 (the display defining `Π_2(y|x, q_1, q_2, ξ)` and the
sentence after it). With `λ ∈ [0, 1]`, `p − b = λp` and `w_2 = λc_2 + b`:
1. `Π_2(y|x, q_1, q_2, ξ) = (1 − λ)(Ω_2(y|q_1, ξ) − c_2 q_1) + c_2 x − w_2 q_1` for all arguments;
2. if `q_1 ≤ x < q_2` and `q_2 ≤ q_2(q_1, ξ)` (`qopt`, a maximizer of `Ω_2(·|q_1, ξ)` over `q_2 ≥ q_1`),
   then delivering in full, `y = q_2`, maximizes the supplier's profit over `x ≤ y ≤ q_2`;
3. ("i.e., the supplier does not satisfy the retailer if the retailer happens to irrationally order
   too much") if `λ < 1`, `q_1 ≤ x < q_2` and `q_2 > q_2(q_1, ξ)`, then `y = q_2` does not maximize the
   supplier's profit over `x ≤ y ≤ q_2`. -/
theorem p65_supplier_fills (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 = lam * M.c2 + b) :
    (∀ x q1 ξ y, M.supplierProfit2Fill w2 b x q1 ξ y =
      (1 - lam) * (M.Omega2 q1 ξ y - M.c2 * q1) + M.c2 * x - w2 * q1) ∧
    (∀ q1 ξ x q2 qopt, 0 ≤ q1 → 0 ≤ ξ → q1 ≤ x → x < q2 →
      q1 ≤ qopt → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) qopt → q2 ≤ qopt →
      IsMaxOn (M.supplierProfit2Fill w2 b x q1 ξ) (Set.Icc x q2) q2) ∧
    (∀ q1 ξ x q2 qopt, 0 ≤ q1 → 0 ≤ ξ → q1 ≤ x → x < q2 →
      q1 ≤ qopt → IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) qopt → lam < 1 → qopt < q2 →
      ¬ IsMaxOn (M.supplierProfit2Fill w2 b x q1 ξ) (Set.Icc x q2) q2) := by sorry

end CachonCoord.DemandUpdate
