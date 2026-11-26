-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseSpendSum_div_card_le_fixedSize
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseSpendSum_div_card_le_fixedSize
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:40:14.579436+00:00
-- url     : https://prove2.me/theorems/d05e5314-8a96-51ed-914d-9a5c69efb7ab
-- title:
--   Fixed Total: fixed Reverse Spend Sum div card le fixed Size
-- statement:
--   Fixed-spend estimate in terms of the original separator density.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L158-L216
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L158-L216

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedReverseSpendSum_div_card_le_fixedSize
    {N s D : ℕ} {theta : ℝ}
    (htheta : 0 < theta)
    (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N)
    (hD0 : 0 < D) (hDN : D < N) :
    fixedReverseSpendSum N s theta D /
        ((fixedSet N s).card : ℝ) ≤
      centralSeparatorProportion N s *
        (1 + centralSeparatorProportion N s *
          ((3 : ℝ) ^ theta - 1)) ^ (D - 1) /
        (((2 : ℝ) ^ D) ^ theta) := by sorry
