-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_pow_le_n
-- name    : ClauseBound.ParityChecks.Params.Big.pow_le_n
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:26:49.323897+00:00
-- url     : https://prove2.me/theorems/13014f72-62d4-492f-abd6-a11128710d86
-- title:
--   Big: pow le n
-- statement:
--   The Big construction uses the pow le n property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L205-L206
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L205-L206

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b

theorem ClauseBound.ParityChecks.Params.Big.pow_le_n : 2 ^ ℓ ≤ n := by sorry
