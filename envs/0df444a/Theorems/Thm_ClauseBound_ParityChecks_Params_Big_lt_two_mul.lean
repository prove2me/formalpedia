-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_lt_two_mul
-- name    : ClauseBound.ParityChecks.Params.Big.lt_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:59.057193+00:00
-- url     : https://prove2.me/theorems/29208ac2-6f2d-4468-8e6f-9b595080cf97
-- title:
--   Big: lt two mul
-- statement:
--   The Big construction uses the lt two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L243-L247
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L243-L247

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

theorem ClauseBound.ParityChecks.Params.Big.lt_two_mul : n < 2 * (nbOf n Δ * LD Δ) := by sorry
