-- Prove2me | Theorems.Thm_DriverSurge_IC_remark_1_q_div
-- name    : DriverSurge.IC.remark_1_q_div
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:21.268984+00:00
-- url     : https://prove2.me/theorems/19a05315-b7bf-41e0-844a-43ae2cf6cbe1
-- title:
--   Remark 1, bullet 3, p. 57 — q_{i→j}(u)/u is strictly decreasing in u
-- statement:
--   For each state $i$ with other state $j$ and positive switching rates,
--   $$u\longmapsto\frac{q_{i\to j}(u)}{u}=\frac{\lambda_{i\to j}}{\lambda_{i\to j}+\lambda_{j\to i}}\cdot\frac{1-e^{-(\lambda_{i\to j}+\lambda_{j\to i})u}}{u}$$
--   is strictly decreasing on $(0,\infty)$.
--
--   This monotonicity is what makes the first term of $r(u,i,w,\sigma)$ monotone in $u$, and hence what fixes the direction of the sign change of $\partial R/\partial u$ in Remark 1's last two bullets.
--
--   **Formalization Note** Lean state `0` is the paper's non-surge state 1 and Lean state `1` the surge state 2; `other i` is the state $j\ne i$.
--
--   Differences from the source:
--   - generalization: D.3.1's standing assumptions (p. 56): $F_i$ has a bounded density, and state 2 dominates state 1 ($\exists\sigma_2$ with $\Delta(\sigma_2,\sigma_1)>0$ for all $\sigma_1$) → not assumed; reason: $q_{i\to j}(u)/u$ depends only on $\lambda_{i\to j},\lambda_{j\to i}$, so the claim holds without them and specializes to the source
-- source:
--   Garg, Nazerzadeh, Driver Surge Pricing, arXiv:1905.07544v4, p. 57, Remark 1 (bullet 3)

import Mathlib
import Definitions.Def_DriverSurge_IC_Model

namespace DriverSurge.IC

open Set

/-- Remark 1, bullet 3 (p. 57): `q_{i→j}(u)/u` is strictly decreasing in `u > 0`. -/
theorem remark_1_q_div (P : Primitives) (i : Fin 2) :
    StrictAntiOn (fun u : ℝ => q P i u / u) (Ioi 0) := by sorry

end DriverSurge.IC
