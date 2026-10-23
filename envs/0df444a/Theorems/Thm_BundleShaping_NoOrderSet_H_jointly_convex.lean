-- Prove2me | Theorems.Thm_BundleShaping_NoOrderSet_H_jointly_convex
-- name    : BundleShaping.NoOrderSet.H_jointly_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:12:06.38962+00:00
-- url     : https://prove2.me/theorems/104b1431-3bd2-46dd-85ef-27257d007736
-- title:
--   §4.2, p. 20 — the expected inventory cost H_t(y, z, q) is jointly convex
-- statement:
--   Consider the bundle-to-stock model with its standing assumptions, and a period $1\le t\le T$. The expected inventory cost
--
--   $$H_t(y,z,q)=b^p_tE(z-d_t)^-+h_tAE(z-d_t)^++h_t(y-Az),$$
--
--   where $y\in\mathbb R^I$ is the item order-up-to level, $z\in\mathbb R^J$ the scheduled bundle production, $q\in\mathbb R^J$ the market-share vector and $d_t=d_t(q,\varepsilon_t)$ the demand (1), is jointly convex in $(y,z,q)$ on $\mathbb R^I\times\mathbb R^J\times\mathbb R^J$.
--
--   Convexity of $H_t$ is the cost-side ingredient of the joint concavity of $G_t$ in Theorem 2(b).
--
--   **Formalization Note.** The paper states the claim "when $b^p_t\ge 0$"; the full standing assumptions are carried, among them $h_t\ge 0$ and $A\ge 0$, which make the aggregated holding cost $\tilde h_t=h_tA$ nonnegative, and the integrability of $\varepsilon_t$, which makes the expectations finite.
-- source:
--   Song & Xue, Demand Shaping Through Bundling and Product Configuration, SSRN 3168907 (version of Aug. 19, 2020), p. 20, §4.2 (sentence after program (9))

import Mathlib
import Definitions.Def_BundleShaping_NoOrderSet_Model

namespace BundleShaping.NoOrderSet

open Matrix

variable {I J : Type} [Fintype I] [Fintype J]

theorem H_jointly_convex (P : Params I J) (hS : P.Standing) (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ P.T) : ConvexOn ℝ Set.univ (fun v : (I → ℝ) × (J → ℝ) × (J → ℝ) => P.H t v.1 v.2.1 v.2.2) := by sorry

end BundleShaping.NoOrderSet
