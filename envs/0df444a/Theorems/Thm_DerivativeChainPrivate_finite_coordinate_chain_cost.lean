-- Prove2me | Theorems.Thm_DerivativeChainPrivate_finite_coordinate_chain_cost
-- name    : DerivativeChainPrivate.finite_coordinate_chain_cost
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:46:44.099055+00:00
-- url     : https://prove2.me/theorems/2eb9bb4a-1a62-4a3d-b256-4ba200dcece1
-- title:
--   Finite northeast chains have bounded total length
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. For $N>0$, if a list has nondecreasing real and imaginary coordinates, then $L(z)\le\sqrt2\,|z_{N-1}-z_0|$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/higher_powers/Source/CoordinateLimits.lean#L54-L78

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.finite_coordinate_chain_cost (n : ℕ) [NeZero n] (z : Fin n → ℂ) (last : Fin n)
    (hlast : last.val=n-1) (hre : Monotone (fun i => (z i).re))
    (him : Monotone (fun i => (z i).im)) :
    chainCost z ≤ Real.sqrt 2*‖z last-z 0‖ := by sorry
