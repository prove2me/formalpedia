-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta_le
-- name    : ClauseBound.ParityChecks.Params.Big.beta_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:21.96522+00:00
-- url     : https://prove2.me/theorems/a58b9914-01cf-4ed9-904e-9cc7737c947c
-- title:
--   Big: beta le
-- statement:
--   The Big construction uses the beta le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L327-L333
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L327-L333

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

theorem ClauseBound.ParityChecks.Params.Big.beta_le : n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2 ≤ 5 * n := by sorry
