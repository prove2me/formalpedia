-- Prove2me | Theorems.Thm_DerivativeChainContinuation_kernel_pair_bounds
-- name    : DerivativeChainContinuation.kernel_pair_bounds
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:28:46.541131+00:00
-- url     : https://prove2.me/theorems/35a397b6-7153-436d-9ba6-b7b65dc17dfb
-- title:
--   Pair-distance bounds for a barycentric kernel
-- statement:
--   Let each row of a nonnegative finite kernel $K$ be a probability distribution on complex points $y_a$, with mean $x_i$. Put $c_i=\sum_aK_{ia}|y_a-x_i|$ and $d_{ij}=\sum_{a,b}K_{ia}K_{jb}|y_a-y_b|$. For every pair of row labels, $$|x_i-x_j|\le d_{ij},\qquad c_i-|x_i-x_j|\le d_{ij}.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/FiniteNormMean.lean#L33-L59

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.kernel_pair_bounds {ι κ : Type*} [Fintype κ]
    (K : ι → κ → ℝ) (x : ι → ℂ) (y : κ → ℂ)
    (hK : ∀ i a, 0 ≤ K i a) (hKs : ∀ i, ∑ a, K i a=1)
    (hKm : ∀ i, ∑ a, (K i a:ℂ)*y a=x i) (i j : ι) :
    ‖x i-x j‖ ≤ kernelPairDistance K y i j ∧
    kernelCost K x y i-‖x i-x j‖ ≤ kernelPairDistance K y i j := by sorry
