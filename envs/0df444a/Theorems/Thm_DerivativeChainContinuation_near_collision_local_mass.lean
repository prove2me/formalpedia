-- Prove2me | Theorems.Thm_DerivativeChainContinuation_near_collision_local_mass
-- name    : DerivativeChainContinuation.near_collision_local_mass
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:39:03.776988+00:00
-- url     : https://prove2.me/theorems/defdd121-07f3-4e98-b2e5-f0a0b5d8e7af
-- title:
--   Local mass converts positive-part charge into mean cost
-- statement:
--   Let $w_i\ge0$, $\sum_iw_i=1$, and suppose every closed radius-$r$ ball centered at $x_i$ has weight at least $\alpha\ge0$. For arbitrary real charges $c_i$, $$\alpha\left(\sum_iw_ic_i-2r\right)\le\sum_{i,j}w_iw_j\max(c_i-2|x_i-x_j|,0).$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/NearCollision.lean#L25-L51

import Mathlib
import Definitions.Def_DerivativeChainContinuation_NearCollision
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.near_collision_local_mass {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (x : ι → ℂ) (c : ι → ℝ) (r a : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i=1) (ha : 0 ≤ a)
    (hmass : ∀ i, a ≤ ∑ j, if ‖x i-x j‖ ≤ r then w j else 0) :
    a*((∑ i, w i*c i)-2*r) ≤ nearCollisionCharge w x c := by sorry
