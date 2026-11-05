-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_cnt_take
-- name    : ClauseBound.ParityChecks.BridgeInc.cnt_take
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:45.713845+00:00
-- url     : https://prove2.me/theorems/c31dd997-fa6d-4e1b-b1d5-61527ae2675b
-- title:
--   Bridge Inc: cnt take
-- statement:
--   The checks before j, cut out of the list of all checks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L206-L209
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L206-L209

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

theorem ClauseBound.ParityChecks.BridgeInc.cnt_take (τ : ℕ → Bool) (ψ : Fml) (Lam : List (List ℕ)) {j j' : ℕ} (h : j' < j) : cnt τ ψ (Lam.take j) j' = cnt τ ψ Lam j' := by sorry
