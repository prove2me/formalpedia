-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedReverseSpendSum_zero
-- name    : CollatzEndpointTransport.FixedTotal.fixedReverseSpendSum_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:40:25.65847+00:00
-- url     : https://prove2.me/theorems/1589ad09-ff90-5fe3-946c-9b48ccd93939
-- title:
--   Fixed Total: fixed Reverse Spend Sum zero
-- statement:
--   The Fixed Total construction uses the fixed Reverse Spend Sum zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L268-L278
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorReverse.lean#L268-L278

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.fixedReverseSpendSum_zero
    {N s : ℕ} {theta : ℝ} :
    fixedReverseSpendSum N s theta 0 = 0 := by sorry
