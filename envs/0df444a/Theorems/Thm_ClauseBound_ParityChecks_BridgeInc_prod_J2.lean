-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_prod_J2
-- name    : ClauseBound.ParityChecks.BridgeInc.prod_J2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:36:18.857345+00:00
-- url     : https://prove2.me/theorems/6e5246c0-911c-4c6b-958d-a0267a571c81
-- title:
--   Bridge Inc: prod J2
-- statement:
--   A product over the one check j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L233-L237
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L233-L237

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

theorem ClauseBound.ParityChecks.BridgeInc.prod_J2 {r j : ℕ} (hj : j < r) (g : ℕ → ℤ) : ∏ j' ∈ J2 r j, g j'.val = g j := by sorry
