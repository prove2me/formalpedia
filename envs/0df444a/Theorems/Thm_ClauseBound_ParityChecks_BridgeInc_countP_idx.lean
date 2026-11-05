-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_countP_idx
-- name    : ClauseBound.ParityChecks.BridgeInc.countP_idx
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:32.946209+00:00
-- url     : https://prove2.me/theorems/94256225-3312-4e2d-88ba-0b6d576ec82e
-- title:
--   Bridge Inc: count P idx
-- statement:
--   The number of members with a property of a list of numbers below m without repetition, as the
--   number of elements of a subset of Fin m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L47-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L47-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

theorem ClauseBound.ParityChecks.BridgeInc.countP_idx {m : ℕ} {I : List ℕ} (hn : I.Nodup) (hlt : ∀ e ∈ I, e < m) (q : ℕ → Bool) :
    I.countP q = #{e : Fin m | e.val ∈ I ∧ q e.val = true} := by sorry
