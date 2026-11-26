-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_centralSourceSet_inr
-- name    : CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:51.614806+00:00
-- url     : https://prove2.me/theorems/1a49e929-155b-4379-89b6-925edcc3e3cb
-- title:
--   Fixed Total: mem central Source Set inr
-- statement:
--   The Fixed Total construction uses the mem central Source Set inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L694-L699
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L694-L699

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

theorem CollatzEndpointTransport.FixedTotal.mem_centralSourceSet_inr
    {M : ℕ} {theta eta : ℝ}
    (u : Fin M) (c : Composition (M - (u : ℕ))) :
    (Sum.inr ⟨u, c⟩ : SourceCode M) ∈ centralSourceSet M theta eta ↔
      CentralRenyiAdmissible (M - (u : ℕ)) c.length theta eta := by sorry
