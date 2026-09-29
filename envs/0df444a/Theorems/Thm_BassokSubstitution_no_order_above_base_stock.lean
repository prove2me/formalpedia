-- Prove2me | Theorems.Thm_BassokSubstitution_no_order_above_base_stock
-- name    : BassokSubstitution.no_order_above_base_stock
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T08:53:07.548338+00:00
-- url     : https://prove2.me/theorems/7c93ed0a-ace5-44ba-aab9-c6db956c99eb
-- title:
--   Theorem 2 — no order for a product stocked at or above its base-stock level
-- statement:
--   Consider the single-period $N$-product model with downward substitution, satisfying Assumptions 1–3, with substitution cost $b \ge 0$ and unit costs $s_i < c_i < p_i + \pi_i$, and with independent nonnegative demands that have densities and finite means and whose laws charge every nonempty open interval of $[0,\infty)$.
--
--   Let $y^* \ge 0$ be a base-stock vector: a maximizer of $P(0, \cdot)$ over the nonnegative orthant. Let $x \ge 0$ be any starting inventory and $\bar y$ any optimal inventory level after ordering, i.e. a maximizer of $P(x,\cdot)$ over $\{y : y \ge x\}$. Then for every product $i$,
--   $$x_i \ge y^*_i \implies \bar y_i = x_i.$$
--
--   No order is placed for a product whose starting inventory is at least its base-stock level, whatever the starting inventory of the other products. With Theorem 1 (order up to $y^*$ when $x \le y^*$) this describes the optimal ordering policy of the substitution model.
--
--   **Formalization Note.** $y^*$ is quantified over all maximizers of $P(0,\cdot)$ on $\{y \ge 0\}$, which are exactly the vectors $y^*$ of Theorem 1; the conclusion is claimed for every optimal $\bar y$. The paper uses without stating: independence of the demand classes, densities and finite means, $s_i < c_i < p_i + \pi_i$, and a unique optimal level $\bar y(x)$; the full-support hypothesis stands in for the latter (without it, a demand density vanishing around the critical fractile gives a flat-topped profit and the universal statement fails already for $N = 1$).
-- source:
--   Bassok, Anupindi, Akella, Single-Period Multiproduct Inventory Models with Substitution, Operations Research 47(4):632–642 (1999), p. 636, Theorem 2

import Mathlib
import Definitions.Def_BassokSubstitution_Profit

open MeasureTheory

namespace BassokSubstitution

/-- Theorem 2 (goal): let `y*` be a base-stock vector, i.e. a maximizer of `P(0, ·)` over the
nonnegative orthant. For every starting inventory `x ≥ 0`, every optimal inventory level
`ȳ` after ordering (a maximizer of `P(x, ·)` over `{y | x ≤ y}`), and every product `i`
with `x_i ≥ y*_i`, no order is placed for product `i`: `ȳ_i = x_i`. -/
theorem no_order_above_base_stock {N : ℕ} (M : Model N)
    (hA1 : M.Assumption1) (hA2 : M.Assumption2) (hA3 : M.Assumption3) (hb : 0 ≤ M.b)
    (hcost : ∀ i, M.s i < M.c i ∧ M.c i < M.p i + M.penalty i)
    (ν : Fin N → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (hν : DemandLaw ν)
    (hsupp : FullSupport ν)
    (ystar : Fin N → ℝ) (hystar_nonneg : 0 ≤ ystar)
    (hystar : IsMaxOn (M.profit (Measure.pi ν) 0) {y | 0 ≤ y} ystar)
    (x : Fin N → ℝ) (hx : 0 ≤ x)
    (ybar : Fin N → ℝ) (hybar_ge : x ≤ ybar)
    (hybar : IsMaxOn (M.profit (Measure.pi ν) x) {y | x ≤ y} ybar)
    (i : Fin N) (hi : ystar i ≤ x i) :
    ybar i = x i := by sorry

end BassokSubstitution
