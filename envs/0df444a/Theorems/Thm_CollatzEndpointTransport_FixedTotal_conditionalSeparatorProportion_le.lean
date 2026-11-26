-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_conditionalSeparatorProportion_le
-- name    : CollatzEndpointTransport.FixedTotal.conditionalSeparatorProportion_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:11.010096+00:00
-- url     : https://prove2.me/theorems/57a894ec-0eec-54a6-88cf-9d4a71c043ba
-- title:
--   Fixed Total: conditional Separator Proportion le
-- statement:
--   The conditional separator density after one forced separator does not
--   exceed the original separator density.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L142-L155
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L142-L155

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.conditionalSeparatorProportion_le
    {N s : ℕ} (hN : 2 < N) (hs1 : 1 < s) (hsN : s < N) :
    (((s - 2 : ℕ) : ℝ) / (N - 2 : ℕ)) ≤
      centralSeparatorProportion N s := by sorry
