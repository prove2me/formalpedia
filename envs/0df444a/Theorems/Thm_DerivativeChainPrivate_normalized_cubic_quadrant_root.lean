-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_cubic_quadrant_root
-- name    : DerivativeChainPrivate.normalized_cubic_quadrant_root
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T03:32:19.801013+00:00
-- url     : https://prove2.me/theorems/96e2b2fc-7d50-4a9a-b543-73aff25fbf11
-- title:
--   Unique positive-real root of the normalized cubic
-- statement:
--   Let $\beta\in\mathbb C$ satisfy $\operatorname{Re}\beta,\operatorname{Im}\beta\ge0$. There is exactly one complex $z$ satisfying $z^3-z=\beta$ and $\operatorname{Re}z>0$. The uniqueness predicate ranges over all such positive-real roots.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L283-L315

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_cubic_quadrant_root (β : ℂ)
    (hβre : 0 ≤ β.re) (hβim : 0 ≤ β.im) :
    ∃! z : ℂ, z ^ 3 - z = β ∧ 0 < z.re := by sorry
