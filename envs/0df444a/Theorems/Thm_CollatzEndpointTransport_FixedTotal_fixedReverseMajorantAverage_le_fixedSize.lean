-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseMajorantAverage_le_fixedSize
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseMajorantAverage_le_fixedSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:34.390159+00:00
-- url     : https://prove2.me/theorems/b7847117-b38a-51c7-a9b4-0ec7f8388f2f
-- title:
--   Fixed Total: fixed Reverse Majorant Average le fixed Size
-- statement:
--   Reverse-majorant average with the fixed-size separator constant.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeCentralRenyiMoment.lean#L26-L73
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeCentralRenyiMoment.lean#L26-L73

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedReverseMajorantAverage_le_fixedSize
    {N s : ℕ} {theta : ℝ}
    (htheta : 0 < theta)
    (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N)
    (hpiAlpha :
      centralSeparatorProportion N s < centralRenyiAlpha theta)
    (hcontract : 3 ^ s ≤ 2 ^ N) :
    fixedReverseMajorantAverage N s theta ≤
      centralSeparatorProportion N s /
        ((2 : ℝ) ^ theta - 1 -
          centralSeparatorProportion N s * ((3 : ℝ) ^ theta - 1)) + 2 := by sorry
