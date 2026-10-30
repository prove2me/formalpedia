-- Prove2me | Theorems.Thm_DerivativeChainContinuation_near_collision_kernel_charge
-- name    : DerivativeChainContinuation.near_collision_kernel_charge
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:31:17.079096+00:00
-- url     : https://prove2.me/theorems/52ed2100-49a0-426b-9505-942253edf01d
-- title:
--   Localized charge is paid by the kernel Gini increment
-- statement:
--   Let $w_i\ge0$ be finite weights and $K$ a nonnegative row-stochastic barycentric kernel from complex points $x_i$ to $y_a$. Write $c_i$ for its mean edge cost and $d_{ij}$ for its conditional pair distance. Then $$\sum_{i,j}w_iw_j\max(c_i-2|x_i-x_j|,0)\le\sum_{i,j}w_iw_jd_{ij}-G(w,x).$$ The weights need not be normalized.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/NearCollision.lean#L10-L23

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainContinuation_NearCollision
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.near_collision_kernel_charge {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (hw : ∀ i, 0 ≤ w i) (hK : ∀ i a, 0 ≤ K i a)
    (hKs : ∀ i, ∑ a, K i a=1) (hKm : ∀ i, ∑ a, (K i a:ℂ)*y a=x i) :
    nearCollisionCharge w x (kernelCost K x y) ≤
      (∑ i, ∑ j, w i*w j*kernelPairDistance K y i j)-finiteGini w x := by sorry
