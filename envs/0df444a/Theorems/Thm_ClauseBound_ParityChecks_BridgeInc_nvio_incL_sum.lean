-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_BridgeInc_nvio_incL_sum
-- name    : ClauseBound.ParityChecks.BridgeInc.nvio_incL_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:50:33.175319+00:00
-- url     : https://prove2.me/theorems/88bdc2f3-014b-4eb1-8fe5-c31003661f50
-- title:
--   Bridge Inc: nvio inc L sum
-- statement:
--   The incidences that τ violates, check by check.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L119-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/BridgeInc.lean#L119-L136

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

theorem ClauseBound.ParityChecks.BridgeInc.nvio_incL_sum (τ : ℕ → Bool) (n : ℕ) (ψ : Fml) (Lam : List (List ℕ)) (j : ℕ) :
    nvio τ (incL n ψ Lam j) = ∑ j' ∈ range j, (if τ (n + j') = true then cnt τ ψ Lam j' else 0) + cnt τ ψ Lam j := by sorry
