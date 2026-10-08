-- Prove2me | Theorems.Thm_CachonCoord_DemandUpdate_p67_supplier_production
-- name    : CachonCoord.DemandUpdate.p67_supplier_production
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:59:14.503307+00:00
-- url     : https://prove2.me/theorems/d0f64cc8-67ee-4009-aa4c-cee51d49d620
-- title:
--   §6.6.1, p. 67 — ∂Π₁(x|q₁)/∂x = −c₁ + c₂(1 − G(ξ(x))), negative at q₁°: the supplier produces exactly q₁°
-- statement:
--   Let $q_2(q_1,\xi)$ be a supply chain optimal period-2 order. The retailer orders it in period 2 and the supplier fills it. Consider the supplier's period-1 expected profit $\Pi_1(x\,|\,q_1)$ as a function of her period-1 production $x$.
--
--   1. If $x \ge q_1$, $x > 0$ and $\xi(x) \ge 0$ solves $F(x\,|\,\xi(x)) = (p-c_2)/p$, then the right derivative of $\Pi_1(\cdot\,|\,q_1)$ at $x$ is
--   $$\frac{\partial \Pi_1(x\,|\,q_1)}{\partial x} = -c_1 + c_2\big(1 - G(\xi(x))\big),$$
--   and for $x > q_1$ this is a two-sided derivative.
--   2. Let $q_1^o > 0$ be a supply chain optimal period-1 order, and let $\xi(q_1^o) \ge 0$ solve (26) at $q_1^o$. Then
--   $$-c_1 + c_2\big(1 - G(\xi(q_1^o))\big) < 0,$$
--   and producing exactly $q_1^o$ is the supplier's unique optimal period-1 production: $\Pi_1(x\,|\,q_1^o) < \Pi_1(q_1^o\,|\,q_1^o)$ for every $x \ge 0$, $x \ne q_1^o$.
--
--   With a coordinating contract the supplier therefore produces just enough to cover the retailer's period-1 order, and no inventory is stranded at the supplier.
--
--   **Formalization Note** At $x = q_1$ the function $\Pi_1(\cdot\,|\,q_1)$ has a kink (its left derivative is $c_2 - c_1$), so the page's $\partial \Pi_1(q_1^o|q_1^o)/\partial x$ is read as a right derivative. These claims do not depend on the contract terms $w_2$, $b$, which enter $\Pi_1$ only through terms constant in $x$, so the statement holds for all $w_2$, $b$. The page's "Hence" is formalized as the unique-maximizer statement.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, p. 67, the two derivative displays and the sentence "Hence, …"

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 67 (the two derivative displays and "Hence, …").
Let `q2sel` select a supply chain optimal period-2 order `q_2(q_1, ξ)`, which the retailer orders
and the supplier fills. For the supplier's period-1 profit `Π_1(x|q_1)` as a function of her
period-1 production `x`:
1. for `x ≥ q_1`, `x > 0`, with `ξ(x)` solving (26) at `x`, the right derivative is
   `−c_1 + c_2(1 − G(ξ(x)))`, and it is a two-sided derivative when `x > q_1`;
2. at a supply chain optimal `q_1° > 0` with `ξ(q_1°)` solving (26),
   `−c_1 + c_2(1 − G(ξ(q_1°))) < 0`, and producing exactly `q_1°` is the supplier's unique
   optimal period-1 production. -/
theorem p67_supplier_production (M : Model) (w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ)
    (hq2 : M.IsChainPeriod2Optimal q2sel) :
    (∀ q1 x xx, 0 ≤ q1 → q1 ≤ x → 0 < x → 0 ≤ xx → M.F xx x = M.ratio →
      HasDerivWithinAt (M.supplierProfit1 w2 b q2sel q1) (-M.c1 + M.c2 * (1 - M.G xx))
        (Set.Ici x) x) ∧
    (∀ q1 x xx, 0 ≤ q1 → q1 < x → 0 ≤ xx → M.F xx x = M.ratio →
      HasDerivAt (M.supplierProfit1 w2 b q2sel q1) (-M.c1 + M.c2 * (1 - M.G xx)) x) ∧
    (∀ q1o xi0, 0 < q1o → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1o →
      0 ≤ xi0 → M.F xi0 q1o = M.ratio →
      -M.c1 + M.c2 * (1 - M.G xi0) < 0 ∧
      ∀ x, 0 ≤ x → x ≠ q1o →
        M.supplierProfit1 w2 b q2sel q1o x < M.supplierProfit1 w2 b q2sel q1o q1o) := by sorry

end CachonCoord.DemandUpdate
