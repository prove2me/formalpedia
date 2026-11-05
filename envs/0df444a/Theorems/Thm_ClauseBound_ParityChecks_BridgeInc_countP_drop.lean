-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_countP_drop
-- name    : ClauseBound.ParityChecks.BridgeInc.countP_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:28.765297+00:00
-- url     : https://prove2.me/theorems/ff160351-ecf2-4956-aba6-4c006384eb81
-- title:
--   Bridge Inc: count P drop
-- statement:
--   The number of members from position t on with a property, as the number of their positions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L28-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L28-L43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Theorems.Thm_Groundwork_PolyT_countP
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.countP
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

theorem ClauseBound.ParityChecks.BridgeInc.countP_drop {α : Type} (p : α → Bool) (d : α) : ∀ (L : List α) (t : ℕ),
    (L.drop t).countP p = #{e : Fin L.length | t ≤ e.val ∧ p (L.getD e.val d) = true}
  := by sorry
