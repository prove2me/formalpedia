-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Bridge_Vof_eq_empty_iff
-- name    : ClauseBound.ParityChecks.Bridge.Vof_eq_empty_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:38:08.427111+00:00
-- url     : https://prove2.me/theorems/d2b30fe6-69b0-472b-858e-feb527292514
-- title:
--   Bridge: Vof eq empty iff
-- statement:
--   ξ violates no clause iff it satisfies the formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L138-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Bridge.lean#L138-L150

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

theorem ClauseBound.ParityChecks.Bridge.Vof_eq_empty_iff {n : ℕ} (ψ : Fml) (ξ : Fin n → Bool) :
    Vof ψ ξ = ∅ ↔ ∀ C ∈ ψ, ∃ l ∈ C, PaddedDescent.F.Mark.ext ξ l.1 = l.2 := by sorry
