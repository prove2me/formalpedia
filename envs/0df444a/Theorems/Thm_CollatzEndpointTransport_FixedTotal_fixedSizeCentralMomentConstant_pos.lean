-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSizeCentralMomentConstant_pos
-- name    : CollatzEndpointTransport.FixedTotal.fixedSizeCentralMomentConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:06:06.765743+00:00
-- url     : https://prove2.me/theorems/be5a26af-d710-54d9-b124-9fca61254ca9
-- title:
--   Fixed Total: fixed Size Central Moment Constant pos
-- statement:
--   The Fixed Total construction uses the fixed Size Central Moment Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeCentralRenyiMoment.lean#L81-L103
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeCentralRenyiMoment.lean#L81-L103

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedSizeCentralMomentConstant_pos
    {theta eta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2) :
    0 < fixedSizeCentralMomentConstant theta eta := by sorry
