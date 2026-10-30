-- Prove2me | Theorems.Thm_DerivativeChainPrivate_normalized_cube_actual_row_values
-- name    : DerivativeChainPrivate.normalized_cube_actual_row_values
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-27T04:00:46.136164+00:00
-- url     : https://prove2.me/theorems/548944d4-48f0-4bdd-a92e-3147907fd412
-- title:
--   Exact derivative rows for the normalized power 3
-- statement:
--   Set $m=3$, $a_m=4$, $b_m=28$. For fixed $m$, let $p_\beta(X)=(X^3-a_mX-b_m\beta)^m$. For every complex $\beta,z$ and each $m\le k<3m$, the stated explicit monic row polynomial is the normalized derivative
--
--   $$R_{m,k}(\beta,z)=\sum_{\substack{u+v+w=m\\3u+v\ge k}}\frac{m!}{u!v!w!}(-a_m)^v(-b_m\beta)^w\frac{(3u+v)!(3m-k)!}{(3u+v-k)!(3m)!}z^{3u+v-k},$$
--
--   where the summation indices are nonnegative integers, and $p_\beta^{(k)}(z)=(3m)!R_{m,k}(\beta,z)/(3m-k)!$. The formal packet lists each rational-coefficient expansion. The final three rows are $z^3-z-\beta$, $z^2-1/3$, and $z$. These are exact derivative identities supporting row selection.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Dependencies/VerifiedCube.lean#L762-L790

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem DerivativeChainPrivate.normalized_cube_actual_row_values (β z : ℂ) :
    let p : Polynomial ℂ := (X ^ 3 - 4 * X - 28 * C β) ^ 3
    (derivative^[3] p).eval z = 504 *
      (z ^ 6 - 5 * z ^ 4 - 20 * β * z ^ 3 + 40/7 * z ^ 2 + 32 * β * z - 16/21 + 28 * β ^ 2) ∧
    (derivative^[4] p).eval z = 3024 *
      (z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + 40/21 * z + 16/3 * β) ∧
    (derivative^[5] p).eval z = 15120 * (z ^ 4 - 2 * z ^ 2 - 4 * β * z + 8/21) ∧
    (derivative^[6] p).eval z = 60480 * (z ^ 3 - z - β) ∧
    (derivative^[7] p).eval z = 60480 * (3 * z ^ 2 - 1) ∧
    (derivative^[8] p).eval z = 362880 * z := by sorry
