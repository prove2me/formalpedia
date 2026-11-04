-- Prove2me | Theorems.Thm_AIMInventory_Known_cost_increment_le
-- name    : AIMInventory.Known.cost_increment_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:29:33.776311+00:00
-- url     : https://prove2.me/theorems/1f767963-3d4b-48a0-b6bc-d73a3fd14a9e
-- title:
--   §2.4 — for 0 ≤ ŷ ≤ y, Q(y) − Q(ŷ) ≤ h·(y − ŷ)
-- statement:
--   Let demand $D \ge 0$ have law $P$ with finite mean, let $h,b > 0$, and let $Q(y) = h\,E[y-D]^+ + b\,E[D-y]^+$. For all levels $0 \le \hat y \le y$,
--   $$Q(y) - Q(\hat y) \le h\,(y - \hat y).$$
--
--   In the non-perishable case the AIM algorithm implements $y_t = \max\{\hat y_t, x_t\} \ge \hat y_t$; this inequality turns the excess cost $Q(y_t) - Q(\hat y_t)$ into $h$ times the excess inventory $y_t - \hat y_t$, which Theorem 6 bounds by a queue.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, p. 10, §2.4 (display after 'Since y_t = max{ŷ_t, x_t}')

import Mathlib
import Definitions.Def_AIMInventory_Known_AIM

namespace AIMInventory.Known

/-- §2.4, p. 10: raising the order-up-to level from `ŷ` to `y ≥ ŷ ≥ 0` raises the expected
one-period cost by at most `h·(y − ŷ)`. -/
theorem cost_increment_le (P : CappedBaseStock.DemandLaw) (h b : ℝ) (hh : 0 < h) (hb : 0 < b)
    (yhat y : ℝ) (hyhat : 0 ≤ yhat) (hle : yhat ≤ y) :
    Q P h b y - Q P h b yhat ≤ h * (y - yhat) := by sorry

end AIMInventory.Known
