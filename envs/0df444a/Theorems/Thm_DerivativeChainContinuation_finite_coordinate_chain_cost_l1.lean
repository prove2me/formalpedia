-- Prove2me | Theorems.Thm_DerivativeChainContinuation_finite_coordinate_chain_cost_l1
-- name    : DerivativeChainContinuation.finite_coordinate_chain_cost_l1
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:13:18.030698+00:00
-- url     : https://prove2.me/theorems/d0afa7fd-ec7e-4d77-a4ad-f1dffc90791e
-- title:
--   Length of a coordinate-monotone chain from its coordinate increments
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. For $N>0$, suppose both real and imaginary coordinates are nondecreasing. With $z_{N-1}$ the final entry,
--
--   $$L(z)\le\operatorname{Re}(z_{N-1}-z_0)+\operatorname{Im}(z_{N-1}-z_0).$$
--
--   This is the coordinate-length budget used by the sharp endpoint estimate.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/SharpChainCost.lean#L8-L37

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainContinuation.finite_coordinate_chain_cost_l1 (n : ℕ) [NeZero n] (z : Fin n → ℂ)
    (last : Fin n) (hlast : last.val=n-1) (hre : Monotone (fun i => (z i).re))
    (him : Monotone (fun i => (z i).im)) :
    chainCost z ≤ (z last).re-(z 0).re+(z last).im-(z 0).im := by sorry
