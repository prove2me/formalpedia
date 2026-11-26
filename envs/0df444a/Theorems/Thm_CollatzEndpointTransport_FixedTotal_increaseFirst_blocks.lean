-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_increaseFirst_blocks
-- name    : CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:21:35.741128+00:00
-- url     : https://prove2.me/theorems/0e20b48e-4683-47bc-8b99-a81830eccea6
-- title:
--   Fixed Total: increase First blocks
-- statement:
--   The Fixed Total construction uses the increase First blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCompositionRecurrence.lean#L205-L209
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalCompositionRecurrence.lean#L205-L209

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section

theorem CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
    {N : ℕ} (hN : 0 < N) (c : Composition N) :
    (increaseFirst hN c).blocks =
      (c.blocks.head (composition_blocks_ne_nil hN c) + 1) :: c.blocks.tail := by sorry

attribute [defeq] CollatzEndpointTransport.FixedTotal.increaseFirst_blocks
