-- Prove2me | Theorems.Thm_DerivativeChainContinuation_rankWeight_square_sum
-- name    : DerivativeChainContinuation.rankWeight_square_sum
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T17:04:41.543789+00:00
-- url     : https://prove2.me/theorems/38b66c7d-2d91-41a6-8d52-2dc45154c77d
-- title:
--   Square sum of the centered rank weights
-- statement:
--   For an integer $m\ge0$, define $w_i=2i+1-m$ for $0\le i<m$. Then
--
--   $$\sum_{i=0}^{m-1}w_i^2=\frac{m(m^2-1)}3.$$
--
--   These exact rank-weight moments enter the Cauchy–Schwarz bound for ordered dispersion.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/RankDispersion.lean#L20-L33

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RankDispersion
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators

theorem DerivativeChainContinuation.rankWeight_square_sum (m : ℕ) :
    (∑ i : Fin m,(rankWeight m i)^2)=(m : ℝ)*((m : ℝ)^2-1)/3 := by sorry
