-- Prove2me | Theorems.Thm_DerivativeChainContinuation_all_scale_compression_bound
-- name    : DerivativeChainContinuation.all_scale_compression_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:29:10.286993+00:00
-- url     : https://prove2.me/theorems/d5727d29-53fd-47c8-bda1-581bbb6482c8
-- title:
--   All-positive-scale compression bounds for centered source roots
-- statement:
--   Let $a_0,\ldots,a_n\in\mathbb C$ with $n>0$, let $z\in\mathbb C$ be arbitrary and $t>0$. Put $b_i=a_i-z$, $d_i=t+|b_i|^2$, $D=\prod_i d_i$, $M_0=(n+1)^{-1}\sum_i1/d_i$, $M_1=(n+1)^{-1}\sum_i b_i/d_i$, $F=tM_0^2+|M_1|^2$, $A=tM_0$, and $\beta=tD\prime/D$, where $D\prime$ is the corresponding product over the actual normalized derivative roots of $\prod_i(X-b_i)$. Set $\Gamma=tF-\beta$. Assume $\sum_i a_i=0$ and let $\delta$ be the source polynomial's Schoenberg deficit. Then $$0\le\Gamma\le A\min(1,\delta/t)\le\min(1,\delta/t),\qquad\Gamma\le A(1-e^{-\delta/t}),\qquad A^2e^{-\delta/t}\le\beta.$$ Repeated roots and every positive squared scale are included; there is no assumption $t>\delta$.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/AllScaleCompression.lean#L26-L108

import Mathlib
import Definitions.Def_DerivativeChainContinuation_AllScaleCompression
import Definitions.Def_DerivativeChainContinuation_RowCovariance
import Definitions.Def_DerivativeChainContinuation_ScaleMoments
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Matrix Polynomial
open scoped BigOperators ComplexOrder

theorem DerivativeChainContinuation.all_scale_compression_bound (n : ℕ) (hn : 0 < n) (a : Fin (n+1) → ℂ)
    (hcenter : ∑ i,a i=0) (z : ℂ) (t : ℝ) (ht : 0 < t) :
    let b := fun i => a i-z;
    let δ := schoenbergDeficit (∏ i,(X-C (a i)));
    0 ≤ scaleCompressionGap b t ∧
      scaleCompressionGap b t ≤ t*scaleMeanZero b t*min 1 (δ/t) ∧
      t*scaleMeanZero b t*min 1 (δ/t) ≤ min 1 (δ/t) ∧
      scaleCompressionGap b t ≤ t*scaleMeanZero b t*(1-Real.exp (-δ/t)) ∧
      (t*scaleMeanZero b t)^2*Real.exp (-δ/t) ≤ t*scaleDerivativeProduct b t/scaleSourceProduct b t := by sorry
