-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_prod_J1
-- name    : ClauseBound.ParityChecks.BridgeInc.prod_J1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:50:45.729723+00:00
-- url     : https://prove2.me/theorems/612bcf47-a76b-429a-a2d7-e4fa74947f77
-- title:
--   Bridge Inc: prod J1
-- statement:
--   A product over the checks before j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L228-L230
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L228-L230

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

theorem ClauseBound.ParityChecks.BridgeInc.prod_J1 {r j : ℕ} (hj : j ≤ r) (g : ℕ → ℤ) : ∏ j' ∈ J1 r j, g j'.val = ∏ j' ∈ range j, g j' := by sorry
