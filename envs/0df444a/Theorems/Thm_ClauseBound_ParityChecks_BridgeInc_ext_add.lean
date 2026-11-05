-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_ext_add
-- name    : ClauseBound.ParityChecks.BridgeInc.ext_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:35.233685+00:00
-- url     : https://prove2.me/theorems/c58c2899-aa96-4b44-80da-dc2dcde8ebb0
-- title:
--   Bridge Inc: ext add
-- statement:
--   The Bridge Inc construction uses the ext add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L71-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L71-L73

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

theorem ClauseBound.ParityChecks.BridgeInc.ext_add {n r : ℕ} (σ : Fin (n + r) → Bool) (j : Fin r) : ext σ (n + j.val) = yy σ j := by sorry
