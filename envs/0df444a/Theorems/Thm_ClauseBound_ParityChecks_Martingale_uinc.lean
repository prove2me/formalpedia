-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_uinc
-- name    : ClauseBound.ParityChecks.Martingale.uinc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:47.552328+00:00
-- url     : https://prove2.me/theorems/5755d99d-988d-4f7a-86dd-d3d8c2b9afb3
-- title:
--   Martingale: uinc
-- statement:
--   One decision, second term.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L122-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L122-L127

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

theorem ClauseBound.ParityChecks.Martingale.uinc (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Uinc nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Uinc nb r j Λ (D.erase e) = Uinc nb r j Λ D := by sorry
