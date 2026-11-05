-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_beta0
-- name    : ClauseBound.ParityChecks.Params.choose_le_beta0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:19.349565+00:00
-- url     : https://prove2.me/theorems/a35161e1-1af0-4fbc-b822-f8ded67f559b
-- title:
--   Params: choose le beta0
-- statement:
--   C(m, nb + 1) ≤ 2^{β₀}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L60-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L60-L60

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
open ClauseBound.ParityChecks.Params

theorem ClauseBound.ParityChecks.Params.choose_le_beta0 (m nb : ℕ) : m.choose (nb + 1) ≤ 2 ^ beta0 m nb := by sorry
