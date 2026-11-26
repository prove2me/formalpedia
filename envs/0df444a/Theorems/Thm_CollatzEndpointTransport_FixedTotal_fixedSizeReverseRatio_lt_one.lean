-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeReverseRatio_lt_one
-- name    : CollatzEndpointTransport.FixedTotal.fixedSizeReverseRatio_lt_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:40:24.904491+00:00
-- url     : https://prove2.me/theorems/31634a03-caaa-490a-be59-3773b7505b6f
-- title:
--   Fixed Total: fixed Size Reverse Ratio lt one
-- statement:
--   The fixed-size ratio is subcritical on the same sharp central window.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L231-L243
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L231-L243

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedSizeReverseRatio_lt_one
    {theta pi : ℝ} (htheta : 0 < theta)
    (hpiAlpha : pi < centralRenyiAlpha theta) :
    fixedSizeReverseRatio theta pi < 1 := by sorry
