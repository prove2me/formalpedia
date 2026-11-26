-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inl
-- name    : CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:13.00783+00:00
-- url     : https://prove2.me/theorems/3cdfce53-3a75-4f65-b61b-4b47c67a76ad
-- title:
--   Fixed Total: mem central Source Set inl
-- statement:
--   The Fixed Total construction uses the mem central Source Set inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L702-L705
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L702-L705

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

theorem CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inl
    {M : ℕ} {theta eta : ℝ} (e : Unit) :
    (Sum.inl e : SourceCode M) ∉ centralSourceSet M theta eta := by sorry
