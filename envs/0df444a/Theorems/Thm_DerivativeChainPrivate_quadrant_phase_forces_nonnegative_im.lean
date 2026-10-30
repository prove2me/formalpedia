-- Prove2me | Theorems.Thm_DerivativeChainPrivate_quadrant_phase_forces_nonnegative_im
-- name    : DerivativeChainPrivate.quadrant_phase_forces_nonnegative_im
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:18:37.723625+00:00
-- url     : https://prove2.me/theorems/cde46f7d-3664-493a-b902-28d3efc9b32d
-- title:
--   A positive inverse phase forces the nonnegative imaginary branch
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. For $z\in\mathbb C$ with $\operatorname{Re}z>0$ and real $k>0$, if $\operatorname{Im}(\beta/z)=2\operatorname{Re}z\operatorname{Im}z\,k$, then $\operatorname{Im}z\ge0$ and $\operatorname{Im}\beta=0\Rightarrow\operatorname{Im}z=0$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L576-L594

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.quadrant_phase_forces_nonnegative_im (β z : ℂ) (k : ℝ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hx : 0 < z.re) (hk : 0 < k)
    (hphase : (β / z).im = 2 * z.re * z.im * k) :
    0 ≤ z.im ∧ (β.im = 0 → z.im = 0) := by sorry
