-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_sum_undRow
-- name    : ClauseBound.ParityChecks.Martingale.sum_undRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:43.309381+00:00
-- url     : https://prove2.me/theorems/f66143bd-0d7b-4bd6-be77-1c478fd25358
-- title:
--   Martingale: sum und Row
-- statement:
--   Before the decision, one pair more is not yet decided.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L110-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L110-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ParityChecksStatement
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_Martingale
set_option autoImplicit false
section
section
open Finset ParityChecks
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Martingale
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

theorem ClauseBound.ParityChecks.Martingale.sum_undRow {r j : ℕ} {D : Finset E} {e : E} (hj : j < r) (he : e ∈ D) :
    ∑ j' ∈ range r, undRow j D j' = ∑ j' ∈ range r, undRow j (D.erase e) j' + 1 := by sorry
