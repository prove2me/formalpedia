-- Prove2me | Theorems.Thm_CollatzEndpointTransport_FixedTotal_fixedSet_card_le_sourceOddLevel
-- name    : CollatzEndpointTransport.FixedTotal.fixedSet_card_le_sourceOddLevel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:01:22.511431+00:00
-- url     : https://prove2.me/theorems/8e5b2eff-1187-5843-bda0-298be2dff350
-- title:
--   Fixed Total: fixed Set card le source Odd Level
-- statement:
--   The Fixed Total construction uses the fixed Set card le source Odd Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L324-L333
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/CentralRenyiShell.lean#L324-L333

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
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralShellCompositionDecidableEq
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralRenyiAdmissibleDecidable

theorem CollatzEndpointTransport.FixedTotal.fixedSet_card_le_sourceOddLevel
    {M s : ℕ} (u : Fin M) (hs : 0 < s) :
    (fixedSet (M - (u : ℕ)) s).card ≤
      (sourceOddLevel M s).card := by sorry
