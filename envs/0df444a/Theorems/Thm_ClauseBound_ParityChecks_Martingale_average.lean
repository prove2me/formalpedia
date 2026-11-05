-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Martingale_average
-- name    : ClauseBound.ParityChecks.Martingale.average
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:05:11.374133+00:00
-- url     : https://prove2.me/theorems/15057b2b-8eeb-4ef5-b776-08da4298a589
-- title:
--   Martingale: average
-- statement:
--   2p + (1 − p) = 1 + p, with the common factor x/(1 + p)^{k+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L60-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Martingale.lean#L60-L62

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

theorem ClauseBound.ParityChecks.Martingale.average (p x : ℚ) (k : ℕ) (hp : 1 + p ≠ 0) : p * (2 * x / (1 + p) ^ (k + 1)) + (1 - p) * (x / (1 + p) ^ (k + 1)) = x / (1 + p) ^ k := by sorry
