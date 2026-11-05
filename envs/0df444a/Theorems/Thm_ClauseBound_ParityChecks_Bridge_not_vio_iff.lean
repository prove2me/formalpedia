-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Bridge_not_vio_iff
-- name    : ClauseBound.ParityChecks.Bridge.not_vio_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:37:49.11951+00:00
-- url     : https://prove2.me/theorems/bd7b4904-07be-40e2-8da4-6750ef0f8d05
-- title:
--   Bridge: not vio iff
-- statement:
--   A clause is not violated iff one of its literals is true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L132-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L132-L135

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_BridgeInc
import Definitions.Def_ClauseBound_ParityChecks_StepOne
import Definitions.Def_ClauseBound_ParityChecks_Bridge
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Bridge
open Groundwork.Prog (Fml)
open PaddedDescent.F.Mark (nvio vio nSat)
open ClauseBound.TopN.EvalW (truncW)
open ClauseBound.ParityChecks ClauseBound.ParityChecks.BridgeInc

theorem ClauseBound.ParityChecks.Bridge.not_vio_iff (σ : ℕ → Bool) (C : List (ℕ × Bool)) : ¬ vio σ C = true ↔ ∃ l ∈ C, σ l.1 = l.2 := by sorry
