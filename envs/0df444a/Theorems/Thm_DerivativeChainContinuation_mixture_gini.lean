-- Prove2me | Theorems.Thm_DerivativeChainContinuation_mixture_gini
-- name    : DerivativeChainContinuation.mixture_gini
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T19:37:22.88235+00:00
-- url     : https://prove2.me/theorems/bce2d63f-ac0a-4953-bc0e-f8c09d5b4c78
-- title:
--   Gini dispersion of a finite kernel mixture
-- statement:
--   For arbitrary finite real weights $w_i$, real kernel entries $K_{ia}$ and complex points $y_a$, $$G(\widetilde w,y)=\sum_{i,j}w_iw_j\sum_{a,b}K_{ia}K_{jb}|y_a-y_b|,\qquad \widetilde w_a=\sum_iw_iK_{ia}.$$ This finite algebraic identity requires no positivity or normalization.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/NearCollisionGini.lean#L6-L23

import Mathlib
import Definitions.Def_DerivativeChainContinuation_FiniteNormMean
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem DerivativeChainContinuation.mixture_gini {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (K : ι → κ → ℝ) (y : κ → ℂ) :
    finiteGini (fun a => ∑ i, w i*K i a) y =
      ∑ i, ∑ j, w i*w j*kernelPairDistance K y i j := by sorry
