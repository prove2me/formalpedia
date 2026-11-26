-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inl
-- name    : CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:58:55.368082+00:00
-- url     : https://prove2.me/theorems/b1c5af4b-073e-5d1f-83fd-9c9097906fd7
-- title:
--   Fixed Total: mem source Late First Odd inl
-- statement:
--   The Fixed Total construction uses the mem source Late First Odd inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L714-L717
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L714-L717

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Definitions.Def_CollatzEndpointTransport_Linear_FiniteFiberMixture
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalActualEndpointMoment
import Definitions.Def_CollatzEndpointTransport_Common_TerrasPrefixEvents
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
set_option autoImplicit false
set_option maxHeartbeats 4000000
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inl
    {M K : ℕ} (e : Unit) :
    (Sum.inl e : SourceCode M) ∈ sourceLateFirstOdd M K := by sorry
