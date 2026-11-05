-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_upar
-- name    : ClauseBound.ParityChecks.Martingale.upar
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:57:41.163626+00:00
-- url     : https://prove2.me/theorems/72dbaff4-0a68-4e25-b0bc-9ecd0a52f107
-- title:
--   Martingale: upar
-- statement:
--   One decision, first term.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L68-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L68-L90

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
omit [Fintype E]

theorem ClauseBound.ParityChecks.Martingale.upar (V : X → Finset E) (nb : ℕ) {r j : ℕ} {Λ : ℕ → Finset E} {D : Finset E} {e : E} (hS : IsState r j Λ D) (he : e ∈ D) :
    pr nb * Upar V nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Upar V nb r j Λ (D.erase e) = Upar V nb r j Λ D := by sorry
