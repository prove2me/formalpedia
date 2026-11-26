-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseSpendSum_le_hypergeometric
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseSpendSum_le_hypergeometric
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:39:57.971179+00:00
-- url     : https://prove2.me/theorems/6b6f7fbf-d3b4-5772-99b4-0f3bace62179
-- title:
--   Fixed Total: fixed Reverse Spend Sum le hypergeometric
-- statement:
--   The exact fixed-size separator moment bounds one terminal-spend slice
--   without the population-size loss from Bernoulli conditioning.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L37-L111
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L37-L111

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedReverseSpendSum_le_hypergeometric
    {N s D : ℕ} {theta : ℝ}
    (htheta : 0 < theta)
    (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N)
    (hD0 : 0 < D) (hDN : D < N) :
    fixedReverseSpendSum N s theta D ≤
      ((N - 2).choose (s - 2) : ℝ) *
        (1 + (((s - 2 : ℕ) : ℝ) / (N - 2 : ℕ)) *
          ((3 : ℝ) ^ theta - 1)) ^ (D - 1) /
        (((2 : ℝ) ^ D) ^ theta) := by sorry
