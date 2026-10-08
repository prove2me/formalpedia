-- Prove2me | Theorems.Thm_CachonCoord_DemandUpdate_p66_supplier_period2
-- name    : CachonCoord.DemandUpdate.p66_supplier_period2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T04:58:28.546535+00:00
-- url     : https://prove2.me/theorems/66403137-ec57-4bb5-905a-cf0c10acb14f
-- title:
--   §6.6.1, p. 66 — the supplier's period-2 profit after filling, strictly increasing in x for x ≤ q₁
-- statement:
--   Take buy back terms with $\lambda \in [0,1]$, $p - b = \lambda p$ and $w_2 - b = \lambda c_2$. When the supplier fills the retailer's order $q_2$ from starting inventory $x$, her period-2 profit satisfies
--   $$\Pi_2(x,q_1,q_2,\xi) = (1-\lambda)\big(\Omega_2(q_2\,|\,q_1,\xi) - c_2 q_1\big) - w_2 q_1 + x c_2 - (x-q_2)^+ c_2 .$$
--   Given $q_2 \ge q_1$, it is strictly increasing in $x$ for $x \le q_1$. Hence the supplier produces and delivers at least the retailer's period-1 order: if the retailer orders the supply chain optimal $q_2(q_1,\xi)$ in period 2, the supplier's period-1 expected profit $\Pi_1(x\,|\,q_1) = -c_1 x + E[\Pi_2(x,q_1,q_2(q_1,\xi),\xi)]$ is strictly increasing in her production $x$ on $[0, q_1]$.
--
--   **Formalization Note** The printed display on p. 66 reads $bS(q_2|\xi) - bq_2 - (q_2-x)^+c_2 = (1-\lambda)\Omega_2(q_2|q_1,\xi) - w_2q_2 + xc_2 - (x-q_2)^+c_2$. Its two sides differ by the constant $(1-\lambda)c_2q_1$, and its left side omits the revenue $w_2(q_2-q_1)$. Both slips are independent of $x$, so the monotonicity claim is unaffected. Here $\Pi_2$ is the p. 65 profit at $y = q_2$, and the identity is stated in its correct form, matching the p. 65 display. The page qualifies the "Hence" sentence with "(as long as $q_1 \le q_1^o$)"; the monotonicity of $\Pi_1(\cdot\,|\,q_1)$ on $[0,q_1]$ holds for every $q_1 \ge 0$, so it is stated without that qualification.
-- source:
--   Cachon (2003), Supply Chain Coordination with Contracts, 3rd draft (Jan. 2003), §6.6.1, p. 66, the display of Π₂(x, q₁, q₂, ξ) and the sentence after it

import Mathlib
import Definitions.Def_CachonCoord_DemandUpdate_Model
import Definitions.Def_CachonCoord_DemandUpdate_Profits

open MeasureTheory ProbabilityTheory

namespace CachonCoord.DemandUpdate

open Model

/-- Cachon (2003), 3rd draft, §6.6.1, p. 66 (the display for `Π_2(x, q_1, q_2, ξ)` and the sentence
after it). With `λ ∈ [0, 1]`, `p − b = λp` and `w_2 − b = λc_2`, the supplier's period-2 profit
after filling the retailer's order `q_2` from starting inventory `x` is
`(1 − λ)(Ω_2(q_2|q_1, ξ) − c_2 q_1) − w_2 q_1 + x c_2 − (x − q_2)⁺ c_2`, and, given `q_2 ≥ q_1`, it is
strictly increasing in `x` for `x ≤ q_1`. Hence ("the supplier surely produces and delivers the
retailer's period 1 order"), when the retailer orders the supply chain optimal `q_2(q_1, ξ)`
(selection `q2sel`) in period 2, the supplier's period-1 expected profit `Π_1(x|q_1)` is strictly
increasing in her period-1 production `x` on `[0, q_1]`. (The printed identity is off by the
constant `(1 − λ)c_2 q_1`; see the Formalization Note.) -/
theorem p66_supplier_period2 (M : Model) (lam w2 b : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hb : M.p - b = lam * M.p) (hw2 : w2 - b = lam * M.c2) :
    (∀ x q1 q2 ξ, M.supplierProfit2 w2 b x q1 q2 ξ =
      (1 - lam) * (M.Omega2 q1 ξ q2 - M.c2 * q1) - w2 * q1 + x * M.c2 - max (x - q2) 0 * M.c2) ∧
    (∀ q1 q2 ξ, q1 ≤ q2 →
      StrictMonoOn (fun x => M.supplierProfit2 w2 b x q1 q2 ξ) (Set.Iic q1)) ∧
    (∀ q2sel : ℝ → ℝ → ℝ, M.IsChainPeriod2Optimal q2sel → ∀ q1, 0 ≤ q1 →
      StrictMonoOn (M.supplierProfit1 w2 b q2sel q1) (Set.Icc 0 q1)) := by sorry

end CachonCoord.DemandUpdate
