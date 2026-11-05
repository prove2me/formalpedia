-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_wf_getD
-- name    : ClauseBound.ParityChecks.BridgeInc.wf_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:37.623141+00:00
-- url     : https://prove2.me/theorems/0ddbfe96-6442-4aa9-8894-d4b6d00e3325
-- title:
--   Bridge Inc: wf get D
-- statement:
--   Every check, and the empty list beyond the last check, is a list without repetition of numbers
--   of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L140-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L140-L145

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

theorem ClauseBound.ParityChecks.BridgeInc.wf_getD {ψ : Fml} {r : ℕ} {Lam : List (List ℕ)} (h : WfC ψ r Lam) (j : ℕ) : (Lam.getD j []).Nodup ∧ ∀ e ∈ Lam.getD j [], e < ψ.length := by sorry
