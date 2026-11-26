-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralDiscardedSourceSet_iff
-- name    : CollatzEndpointTransport.FixedTotal.mem_centralDiscardedSourceSet_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:31.279795+00:00
-- url     : https://prove2.me/theorems/a3df1e5f-be95-4bf2-8b8a-37af555ef36e
-- title:
--   Fixed Total: mem central Discarded Source Set iff
-- statement:
--   The Fixed Total construction uses the mem central Discarded Source Set iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L707-L711
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L707-L711

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

theorem CollatzEndpointTransport.FixedTotal.mem_centralDiscardedSourceSet_iff
    {M : ℕ} {theta eta : ℝ} {x : SourceCode M} :
    x ∈ centralDiscardedSourceSet M theta eta ↔
      x ∉ centralSourceSet M theta eta := by sorry
