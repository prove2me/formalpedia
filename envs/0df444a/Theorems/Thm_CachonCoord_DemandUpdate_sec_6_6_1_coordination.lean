-- Prove2me | Theorems.Thm_CachonCoord_DemandUpdate_sec_6_6_1_coordination
-- name    : CachonCoord.DemandUpdate.sec_6_6_1_coordination
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T05:07:46.055176+00:00
-- url     : https://prove2.me/theorems/ebea4e7a-bd12-4937-bf3c-19c0326c2cc2
-- title:
--   §6.6.1, pp. 65–67 — the buy back contract with p − b = λp, w₂ − b = λc₂, w₁ − w₂ + λc₂ = λc₁ coordinates the newsvendor with demand updating
-- statement:
--   In the newsvendor with one forecast update, let $q_2(q_1,\xi)$ be a supply chain optimal period-2 order. Take the buy back contract $\{w_1, w_2, b\}$ with $\lambda \in [0,1]$ and
--   $$p - b = \lambda p, \qquad w_2 - b = \lambda c_2, \qquad w_1 - w_2 + \lambda c_2 = \lambda c_1 .$$
--   Then:
--
--   1. $\pi_2(q_2\,|\,q_1,\xi) = \lambda\big(\Omega_2(q_2\,|\,q_1,\xi) - c_2 q_1\big) + w_2 q_1$ for all $q_1, \xi, q_2$. Every supply chain optimal period-2 order (over $q_2 \ge q_1$) is optimal for the retailer, and conversely when $\lambda > 0$.
--   2. $\pi_1(q_1) = \lambda\,\Omega_1(q_1)$ for every $q_1 \ge 0$. Every supply chain optimal period-1 order is optimal for the retailer, and conversely when $\lambda > 0$.
--   3. The supplier's period-2 margin is
--   $$w_2 - c_2 = w_1 - \big(\lambda c_1 + (1-\lambda)c_2\big),$$
--   which is strictly smaller than her period-1 margin $w_1 - c_1$ when $\lambda < 1$, and equal to it when $\lambda = 1$.
--
--   The contract coordinates both of the retailer's ordering decisions and gives him the share $\lambda$ of the supply chain's profit. The supplier's later production carries the lower margin.
--
--   **Formalization Note** Optimality is over $q_2 \ge q_1$ in period 2 and $q_1 \ge 0$ in period 1. At $\lambda = 0$ the retailer is indifferent, so the converse directions need $\lambda > 0$. The page's strict margin inequality fails at $\lambda = 1$ (equality), which is stated separately. The supplier's compliance (pp. 65–67) is in the companion milestones.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, pp. 65–67

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, pp. 65–67: the buy back contract `{w_1, w_2, b}` with
`λ ∈ [0, 1]`, `p − b = λp`, `w_2 − b = λc_2` and `w_1 − w_2 + λc_2 = λc_1` coordinates the
newsvendor with demand updating:
1. `π_2(q_2|q_1, ξ) = λ(Ω_2(q_2|q_1, ξ) − c_2 q_1) + w_2 q_1`, so the supply chain's period-2
   optimum is the retailer's (and conversely for `λ > 0`);
2. `π_1(q_1) = λΩ_1(q_1)` for `q_1 ≥ 0`, so the supply chain's period-1 optimum is the retailer's
   (and conversely for `λ > 0`);
3. `w_2 − c_2 = w_1 − (λc_1 + (1 − λ)c_2)`, which is `< w_1 − c_1` for `λ < 1` (`=` at `λ = 1`). -/
theorem sec_6_6_1_coordination (M : Model) (lam w1 w2 b : ℝ) (q2sel : ℝ → ℝ → ℝ)
    (hq2 : M.IsChainPeriod2Optimal q2sel) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2)
    (hw1 : w1 - w2 + lam * M.c2 = lam * M.c1) :
    (∀ q1 ξ q2, M.retailerProfit2 w2 b q1 ξ q2 = lam * (M.Omega2 q1 ξ q2 - M.c2 * q1) + w2 * q1) ∧
    (∀ q1 ξ q2, IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2) ∧
    (0 < lam → ∀ q1 ξ q2, IsMaxOn (M.retailerProfit2 w2 b q1 ξ) (Set.Ici q1) q2 →
      IsMaxOn (M.Omega2 q1 ξ) (Set.Ici q1) q2) ∧
    (∀ q1, 0 ≤ q1 → M.retailerProfit1 w1 w2 b q2sel q1 = lam * M.Omega1 q2sel q1) ∧
    (∀ q1, 0 ≤ q1 → IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1 →
      IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1) ∧
    (0 < lam → ∀ q1, 0 ≤ q1 → IsMaxOn (M.retailerProfit1 w1 w2 b q2sel) (Set.Ici 0) q1 →
      IsMaxOn (M.Omega1 q2sel) (Set.Ici 0) q1) ∧
    w2 - M.c2 = w1 - (lam * M.c1 + (1 - lam) * M.c2) ∧
    (lam < 1 → w2 - M.c2 < w1 - M.c1) ∧
    (lam = 1 → w2 - M.c2 = w1 - M.c1) := by sorry

end CachonCoord.DemandUpdate
