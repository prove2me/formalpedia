-- Prove2me | Theorems.Thm_DerivativeChainContinuation_exists_oriented_square_root
-- name    : DerivativeChainContinuation.exists_oriented_square_root
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:31:07.767978+00:00
-- url     : https://prove2.me/theorems/eadfee96-1bcd-497a-882a-ae0b812d0bee
-- title:
--   A complex square root with a fixed orientation
-- statement:
--   For every $z\in\mathbb C$ there is $d\in\mathbb C$ with $d^2=z$, $\operatorname{Re}d\ge0$, and $\operatorname{Re}d=0\Rightarrow\operatorname{Im}d\le0$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/OrientedSquareRoot.lean#L5-L19

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.exists_oriented_square_root (z : ℂ) :
    ∃ d : ℂ, d^2=z ∧ 0 ≤ d.re ∧ (d.re=0 → d.im ≤ 0) := by sorry
