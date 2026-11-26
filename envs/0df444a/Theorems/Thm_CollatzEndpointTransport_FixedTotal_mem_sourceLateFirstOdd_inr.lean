-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_mem_sourceLateFirstOdd_inr
-- name    : CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:48.656346+00:00
-- url     : https://prove2.me/theorems/1657a2a8-1004-4351-b627-2959885db5a9
-- title:
--   Fixed Total: mem source Late First Odd inr
-- statement:
--   The Fixed Total construction uses the mem source Late First Odd inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L720-L724
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L720-L724

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

theorem CollatzEndpointTransport.FixedTotal.mem_sourceLateFirstOdd_inr
    {M K : ℕ} (u : Fin M) (c : Composition (M - (u : ℕ))) :
    (Sum.inr ⟨u, c⟩ : SourceCode M) ∈ sourceLateFirstOdd M K ↔
      K ≤ (u : ℕ) := by sorry
