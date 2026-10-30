-- Prove2me | Theorems.Thm_DerivativeChainContinuation_scale_gram_factor_bound
-- name    : DerivativeChainContinuation.scale_gram_factor_bound
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:16:32.935779+00:00
-- url     : https://prove2.me/theorems/248d05e0-443b-4d2b-aedb-806211ade471
-- title:
--   Uniform bounds for positive-scale root moments
-- statement:
--   For a nonempty finite complex list and $t>0$, let $M_0=n^{-1}\sum_i(t+|a_i|^2)^{-1}$, $M_1=n^{-1}\sum_i a_i/(t+|a_i|^2)$ and $F=tM_0^2+|M_1|^2$. Then $$0\le F,\qquad tF\le tM_0\le1.$$
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/ScaleMoments.lean#L33-L46

import Mathlib
import Definitions.Def_DerivativeChainContinuation_ScaleMoments
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem DerivativeChainContinuation.scale_gram_factor_bound {n : ℕ} (hn : n ≠ 0) (a : Fin n → ℂ) (t : ℝ) (ht : 0 < t) :
    0 ≤ scaleGramFactor a t ∧ t*scaleGramFactor a t ≤ t*scaleMeanZero a t ∧
      t*scaleMeanZero a t ≤ 1 := by sorry
