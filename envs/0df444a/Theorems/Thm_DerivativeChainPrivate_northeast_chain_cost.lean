-- Prove2me | Theorems.Thm_DerivativeChainPrivate_northeast_chain_cost
-- name    : DerivativeChainPrivate.northeast_chain_cost
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T02:43:14.982515+00:00
-- url     : https://prove2.me/theorems/0b647f0a-9edb-4c5d-ab67-24b7295fd8d7
-- title:
--   Euclidean bound for northeast chain length
-- statement:
--   For a finite complex list $z_0,\ldots,z_{N-1}$ write $L(z)=\sum_{i=0}^{N-2}|z_{i+1}-z_i|$. Let $z:\mathbb N\to\mathbb C$ and $N\ge0$. If both coordinates of its first $N$ entries are nondecreasing, then
--
--   $$L((z_i)_{i<N})\le\sqrt2\,|z_{N-1}-z_0|.$$
--
--   For $N=0$, the length is zero and the natural subtraction gives $N-1=0$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L174-L204

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.northeast_chain_cost (n : ℕ) (z : ℕ → ℂ)
    (hre : ∀ i < n - 1, (z i).re ≤ (z (i + 1)).re)
    (him : ∀ i < n - 1, (z i).im ≤ (z (i + 1)).im) :
    chainCost (fun i : Fin n => z i.val) ≤
      Real.sqrt 2 * ‖z (n - 1) - z 0‖ := by sorry
