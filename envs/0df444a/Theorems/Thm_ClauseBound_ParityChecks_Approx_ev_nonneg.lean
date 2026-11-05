-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Approx_ev_nonneg
-- name    : ClauseBound.ParityChecks.Approx.ev_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:55:28.994884+00:00
-- url     : https://prove2.me/theorems/c2b463a7-2ecf-4eee-bc0a-af86eecd9497
-- title:
--   Approx: ev nonneg
-- statement:
--   [q even] is 0 or 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Approx.lean#L32-L33

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

theorem ClauseBound.ParityChecks.Approx.ev_nonneg (q : ℕ) : 0 ≤ ev q := by sorry
