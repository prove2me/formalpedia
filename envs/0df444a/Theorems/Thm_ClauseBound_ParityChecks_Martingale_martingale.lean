-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_martingale
-- name    : ClauseBound.ParityChecks.Martingale.martingale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:58:58.918988+00:00
-- url     : https://prove2.me/theorems/a51961ea-9fd9-4726-b511-db79326ad1b4
-- title:
--   Martingale: martingale
-- statement:
--   One decision: p·Υ^in + (1 − p)·Υ^out = Υ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L192-L198
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L192-L198

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

theorem ClauseBound.ParityChecks.Martingale.martingale : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (e : E),
    2 ≤ nb → IsState r j Λ D → e ∈ D →
    pr nb * Ups V nb r j (putIn j Λ e) (D.erase e) + (1 - pr nb) * Ups V nb r j Λ (D.erase e) = Ups V nb r j Λ D := by sorry
