-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_hyp
-- name    : ClauseBound.ParityChecks.Params.Big.hyp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:29:45.763066+00:00
-- url     : https://prove2.me/theorems/f2479046-c4bf-4d4c-9432-de95632d3797
-- title:
--   Big: hyp
-- statement:
--   All that the run needs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L508-L522
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L508-L522

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

theorem ClauseBound.ParityChecks.Params.Big.hyp : Hyp (parOf n Δ m) (2 ^ n) (2 / 2 ^ (10 * n)) := by sorry
