-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_undRow_ne
-- name    : ClauseBound.ParityChecks.Martingale.undRow_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:18.196653+00:00
-- url     : https://prove2.me/theorems/82a34265-488e-499a-9fbf-e0139099407e
-- title:
--   Martingale: und Row ne
-- statement:
--   For the other checks D does not matter.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L107-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L107-L107

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
omit [DecidableEq E]

theorem ClauseBound.ParityChecks.Martingale.undRow_ne {j j' : ℕ} (h : j' ≠ j) (D D' : Finset E) : undRow j D j' = undRow j D' j' := by sorry
