-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_vio_append
-- name    : ClauseBound.ParityChecks.BridgeInc.vio_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:35.782697+00:00
-- url     : https://prove2.me/theorems/e074744e-d556-4954-a115-cc1c7f38280f
-- title:
--   Bridge Inc: vio append
-- statement:
--   A clause with the dummy literal of check j added is violated if and only if the clause is
--   violated and the dummy variable is 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L93-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L93-L94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_NetDefs
import Definitions.Def_ClauseBound_ParityChecks_Dummy
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
set_option autoImplicit false
section
section
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

theorem ClauseBound.ParityChecks.BridgeInc.vio_append (τ : ℕ → Bool) (C : Cl) (x : ℕ) : vio τ (C ++ [(x, false)]) = (vio τ C && τ x) := by sorry
