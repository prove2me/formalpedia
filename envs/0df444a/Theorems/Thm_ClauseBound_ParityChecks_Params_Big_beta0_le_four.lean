-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta0_le_four
-- name    : ClauseBound.ParityChecks.Params.Big.beta0_le_four
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:00.550532+00:00
-- url     : https://prove2.me/theorems/c4b774f6-c5a3-4171-af57-1abfe40fc52f
-- title:
--   Big: beta0 le four
-- statement:
--   The Big construction uses the beta0 le four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L335-L339
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L335-L339

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

theorem ClauseBound.ParityChecks.Params.Big.beta0_le_four : beta0 m (nbOf n Δ) ≤ 4 * n := by sorry
