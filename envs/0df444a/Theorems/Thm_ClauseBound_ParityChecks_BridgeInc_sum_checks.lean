-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_sum_checks
-- name    : ClauseBound.ParityChecks.BridgeInc.sum_checks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:50:45.139761+00:00
-- url     : https://prove2.me/theorems/2bd78230-a7d8-4548-8db7-06ad1a9c2189
-- title:
--   Bridge Inc: sum checks
-- statement:
--   A sum over the checks, with the checks before j counted if their dummy variable is 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L168-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L168-L175

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

theorem ClauseBound.ParityChecks.BridgeInc.sum_checks {n r : ℕ} (σ : Fin (n + r) → Bool) (c : ℕ → ℕ) {j : ℕ} (hj : j ≤ r) :
    ∑ j' ∈ range j, (if ext σ (n + j') = true then c j' else 0) = ∑ j' : Fin r, if j' ∈ J1 r j ∧ yy σ j' = true then c j'.val else 0 := by sorry
