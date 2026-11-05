-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Approx_ev_le_one
-- name    : ClauseBound.ParityChecks.Approx.ev_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:30.479453+00:00
-- url     : https://prove2.me/theorems/9bd00cbd-f64d-4081-bb4f-365bd966eed5
-- title:
--   Approx: ev le one
-- statement:
--   [q even] is 0 or 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L36-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L36-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic
import Definitions.Def_ClauseBound_ParityChecks_Approx
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Approx
open Finset _root_.ParityChecks
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

theorem ClauseBound.ParityChecks.Approx.ev_le_one (q : ℕ) : ev q ≤ 1 := by sorry
