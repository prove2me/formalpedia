-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_listOddCount_ofFn
-- name    : CollatzEndpointTransport.FixedTotal.listOddCount_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:52:05.49668+00:00
-- url     : https://prove2.me/theorems/1566576e-90be-4284-9bff-17c03b0873c1
-- title:
--   Fixed Total: list Odd Count of Fn
-- statement:
--   The Fixed Total construction uses the list Odd Count of Fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalSourceCoding.lean#L113-L117
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalSourceCoding.lean#L113-L117

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalSourceCoding
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.listOddCount_ofFn
    {M : ℕ} (v : Fin M → Bool) :
    listOddCount (List.ofFn v) = Terras.wordWeight v := by sorry
